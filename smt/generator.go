package smt

import (
	"bytes"
	"fault/ast"
	"fault/llvm"
	"fault/smt/forks"
	"fault/smt/rules"
	"fault/smt/variables"
	"fault/util"
	"fmt"
	"strconv"
	"strings"

	"github.com/llir/llvm/asm"
	"github.com/llir/llvm/ir"
	"github.com/llir/llvm/ir/constant"
	irtypes "github.com/llir/llvm/ir/types"
	"github.com/llir/llvm/ir/value"
)

type Generator struct {
	currentFunction string
	currentBlock    string
	branchId        int

	// Raw input
	Uncertains map[string][]float64
	Unknowns   []string
	functions  map[string]*ir.Func
	rawAsserts []*ast.AssertionStatement
	rawAssumes []*ast.AssertionStatement
	rawRules   [][]rules.Rule

	// Generated SMT
	inits     []string
	constants []string
	rules     []string
	asserts   []string

	variables      *variables.VarData
	blocks         map[string][]rules.Rule
	localCallstack []string

	forks            []forks.Fork
	storedChoice     map[string]*rules.StateChange
	inPhiState       *forks.PhiState //Flag, are we in a conditional or parallel?
	parallelGrouping string
	parallelRunStart bool            //Flag, make sure all branches with parallel runs begin from the same point
	returnVoid       *forks.PhiState //Flag, escape parseFunc before moving to next block

	Rounds     int
	RoundVars  [][][]string
	RVarLookup map[string][][]int
	Results    map[string][]*variables.VarChange
}

func NewGenerator() *Generator {
	return &Generator{
		variables:       variables.NewVariables(),
		functions:       make(map[string]*ir.Func),
		blocks:          make(map[string][]rules.Rule),
		storedChoice:    make(map[string]*rules.StateChange),
		currentFunction: "@__run",
		Uncertains:      make(map[string][]float64),
		inPhiState:      forks.NewPhiState(),
		returnVoid:      forks.NewPhiState(),
		Results:         make(map[string][]*variables.VarChange),
		RVarLookup:      make(map[string][][]int),
	}
}

func Execute(compiler *llvm.Compiler) *Generator {
	generator := NewGenerator()
	generator.LoadMeta(compiler.RunRound, compiler.Uncertains, compiler.Unknowns, compiler.Asserts, compiler.Assumes)
	generator.Run(compiler.GetIR())
	return generator
}

func (g *Generator) LoadMeta(runs int16, uncertains map[string][]float64, unknowns []string, asserts []*ast.AssertionStatement, assumes []*ast.AssertionStatement) {
	if runs == 0 {
		g.Rounds = 1 //even if runs are zero we need to generate asserts for initialization
	} else {
		g.Rounds = int(runs)
	}

	g.Uncertains = uncertains
	g.Unknowns = unknowns
	g.rawAsserts = asserts
	g.rawAssumes = assumes
}

func (g *Generator) Run(llopt string) {
	m, err := asm.ParseString("", llopt) //"/" because ParseString has a path variable
	if err != nil {
		panic(err)
	}
	g.newCallgraph(m)

}

func (g *Generator) newRound() {
	g.RoundVars = append(g.RoundVars, [][]string{})
}

func (g *Generator) initVarRound(base string, num int) {
	g.RoundVars = [][][]string{{{base, fmt.Sprint(num)}}}
}

func (g *Generator) currentRound() int {
	return len(g.RoundVars) - 1
}

func (g *Generator) addVarToRound(base string, num int) {
	if g.currentRound() == -1 {
		g.initVarRound(base, num)
		g.addVarToRoundLookup(base, num, 0, len(g.RoundVars[g.currentRound()])-1)
		return
	}

	g.RoundVars[g.currentRound()] = append(g.RoundVars[g.currentRound()], []string{base, fmt.Sprint(num)})
	g.addVarToRoundLookup(base, num, g.currentRound(), len(g.RoundVars[g.currentRound()])-1)
}

func (g *Generator) addVarToRoundLookup(base string, num int, idx int, idx2 int) {
	g.RVarLookup[base] = append(g.RVarLookup[base], []int{num, idx, idx2})
}

func (g *Generator) lookupVarRounds(base string, num string) [][]int {
	if num == "" {
		return g.RVarLookup[base]
	}

	state, err := strconv.Atoi(num)
	if err != nil {
		panic(err)
	}

	return g.lookupVarSpecificState(base, state)
}

func (g *Generator) lookupVarSpecificState(base string, state int) [][]int {
	for _, b := range g.RVarLookup[base] {
		if b[0] == state {
			return [][]int{b}
		}
	}
	panic(fmt.Errorf("state %d of variable %s is missing", state, base))
}

func (g *Generator) varRounds(base string, num string) map[int][]string {
	ir := make(map[int][]string)
	states := g.lookupVarRounds(base, num)
	for _, s := range states {
		ir[s[1]] = append(ir[s[1]], fmt.Sprintf("%s_%d", base, s[0]))
	}
	return ir
}

func (g *Generator) newFork() {
	if len(g.forks) == 0 {
		g.forks = append(g.forks, forks.Fork{})
		return
	}

	if g.inPhiState.Check() {
		g.forks = append(g.forks[0:len(g.forks)-1], forks.Fork{})
	} else {
		g.forks = append(g.forks, forks.Fork{})
	}
}

func (g *Generator) GetForks() []forks.Fork {
	return g.forks
}

func (g *Generator) getCurrentFork() forks.Fork {
	return g.forks[len(g.forks)-1]
}

func (g *Generator) buildForkChoice(rules []rules.Rule, b string) {
	var stateChanges []string
	fork := g.getCurrentFork()
	for _, ru := range rules {
		stateChanges = append(stateChanges, g.allStateChangesInRule(ru)...)
	}

	seenVar := make(map[string]bool)
	for _, s := range stateChanges {
		base, i := g.variables.GetVarBase(s)
		n := int16(i)
		// Have we seen this variable in a previous branch of
		// this fork?
		if _, ok := fork[base]; ok {
			if seenVar[base] && // Have we seen this variable before?
				fork[base][len(fork[base])-1].Branch == b { // in this branch?
				fork[base][len(fork[base])-1] = fork[base][len(fork[base])-1].AddChoiceValue(n)
			} else {
				seenVar[base] = true
				fork[base] = append(fork[base], g.newChoice(base, n, b))
			}
		} else {
			seenVar[base] = true
			fork[base] = []*forks.Choice{g.newChoice(base, n, b)}
		}
	}
	g.forks[len(g.forks)-1] = fork
}

func (g *Generator) newChoice(base string, n int16, b string) *forks.Choice {
	return &forks.Choice{
		Base:   base,
		Branch: b,
		Values: []int16{n},
	}
}

func (g *Generator) newConstants(globals []*ir.Global) []string {
	// Constants cannot be changed and therefore don't increment
	// in SSA. So instead of return a *rule we can skip directly
	// to a set of strings
	r := []string{}
	for _, gl := range globals {
		id := g.variables.FormatIdent(gl.GlobalIdent.Ident())
		r = append(r, g.constantRule(id, gl.Init))
	}
	return r
}

func (g *Generator) newAssumes(asserts []*ast.AssertionStatement) {
	for _, v := range asserts {
		a := g.parseAssert(v)
		rule := g.writeAssert("", a)
		g.asserts = append(g.asserts, rule)
	}
}

func (g *Generator) newAsserts(asserts []*ast.AssertionStatement) {
	var arule []string
	for _, v := range asserts {
		a := g.parseAssert(v)
		arule = append(arule, a)
	}

	if len(arule) == 0 {
		return
	}

	if len(arule) > 1 {
		g.asserts = append(g.asserts, g.writeAssert("or", strings.Join(arule, "")))
	} else {
		g.asserts = append(g.asserts, g.writeAssert("", arule[0]))
	}
}

func (g *Generator) sortFuncs(funcs []*ir.Func) {
	//Iterate through all the function blocks and store them by
	// function call name.
	for _, f := range funcs {
		// Get function name.
		fname := f.Ident()

		if fname != "@__run" {
			g.functions[f.Ident()] = f
			continue
		}
	}
}

func (g *Generator) newCallgraph(m *ir.Module) {
	g.constants = g.newConstants(m.Globals)
	g.sortFuncs(m.Funcs)

	run := g.parseRunBlock(m.Funcs)
	g.rawRules = append(g.rawRules, run)

	g.rules = append(g.rules, g.generateRules()...)

	g.newAsserts(g.rawAsserts)
	g.newAssumes(g.rawAssumes)

}

func (g *Generator) generateFromCallstack(callstack []string) []rules.Rule {
	if len(callstack) == 0 {
		return []rules.Rule{}
	}

	if len(callstack) > 1 {
		//Generate parallel runs

		perm := g.parallelPermutations(callstack)
		return g.runParallel(perm)
	} else {
		fname := callstack[0]
		v := g.functions[fname]
		return g.parseFunction(v)
	}
}

////////////////////////
// Parsing LLVM IR
///////////////////////

func (g *Generator) parseRunBlock(fns []*ir.Func) []rules.Rule {
	var r []rules.Rule
	for _, f := range fns {
		fname := f.Ident()

		if fname != "@__run" {
			continue
		}

		r = g.parseFunction(f)
	}
	return r
}

func (g *Generator) parseFunction(f *ir.Func) []rules.Rule {
	var ru []rules.Rule

	if g.isBuiltIn(f.Ident()) {
		return ru
	}

	oldfunc := g.currentFunction
	g.currentFunction = f.Ident()

	for _, block := range f.Blocks {
		if !g.returnVoid.Check() {
			r := g.parseBlock(block)
			ru = append(ru, r...)
		}
	}

	g.returnVoid.Out()

	g.currentFunction = oldfunc
	return ru
}

func (g *Generator) parseBlock(block *ir.Block) []rules.Rule {
	var ru []rules.Rule
	oldBlock := g.currentBlock
	g.currentBlock = block.Ident()

	// For each non-branching instruction of the basic block.
	r := g.parseInstruct(block)
	ru = append(ru, r...)

	for k, v := range g.storedChoice {
		r0 := g.stateRules(k, v)
		ru = append(ru, r0)
	}

	//Make sure call stack is clear
	r1 := g.executeCallstack()
	ru = append(ru, r1...)

	var r2 []rules.Rule
	switch term := block.Term.(type) {
	case *ir.TermCondBr:
		r2 = g.parseTermCon(term)
	case *ir.TermRet:
		g.returnVoid.In()
	}
	ru = append(ru, r2...)

	g.currentBlock = oldBlock
	return ru
}

func (g *Generator) parseTermCon(term *ir.TermCondBr) []rules.Rule {
	var ru []rules.Rule
	var cond rules.Rule
	var phis map[string]int16

	g.inPhiState.In()
	id := term.Cond.Ident()
	if g.variables.IsTemp(id) {
		refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
		if v, ok := g.variables.Ref[refname]; ok {
			cond = v
		}
	} else if g.variables.IsBoolean(id) ||
		g.variables.IsNumeric(id) {
		cond = &rules.Wrap{Value: id}
	}
	g.inPhiState.Out()

	g.variables.InitPhis()

	t, f, a := g.parseTerms(term.Succs())

	if !g.isBranchClosed(t, f) {
		var tEnds, fEnds []rules.Rule
		ru = append(ru, t...)
		ru = append(ru, f...)

		g.inPhiState.In() //We need to step back into a Phi state to make sure multiconditionals are handling correctly
		g.newFork()
		g.buildForkChoice(t, "true")
		g.buildForkChoice(f, "false")

		tEnds, phis = g.capCond("true", make(map[string]int16))
		fEnds, _ = g.capCond("false", phis)

		// Keep variable names in sync across branches
		syncs := g.capCondSyncRules([]string{"true", "false"})
		tEnds = append(tEnds, syncs["true"]...)
		fEnds = append(fEnds, syncs["false"]...)

		ru = append(ru, &rules.Ite{Cond: cond, T: tEnds, F: fEnds})
		g.inPhiState.Out()
	}

	g.variables.PopPhis()
	g.variables.AppendState(phis)

	if a != nil {
		after := g.parseAfterBlock(a)
		ru = append(ru, after...)
	}

	return ru
}

func (g *Generator) parseAfterBlock(term *ir.Block) []rules.Rule {
	a := g.parseBlock(term)
	a1 := g.executeCallstack()
	a = append(a, a1...)
	return a
}

func (g *Generator) parseInstruct(block *ir.Block) []rules.Rule {
	var ru []rules.Rule
	for _, inst := range block.Insts {
		// Type switch on instruction to find call instructions.
		switch inst := inst.(type) {
		case *ir.InstAlloca:
			//Do nothing
		case *ir.InstLoad:
			g.loadsRule(inst)
		case *ir.InstStore:
			vname := inst.Dst.Ident()
			if vname == "@__rounds" {
				//Clear the callstack first
				r := g.executeCallstack()
				ru = append(ru, r...)
				g.rawRules = append(g.rawRules, ru)
				ru = []rules.Rule{}

				//Initate new round
				g.newRound()
				continue
			}

			if vname == "@__parallelGroup" {
				continue
			}

			switch inst.Src.Type().(type) {
			case *irtypes.ArrayType:
				refname := fmt.Sprintf("%s-%s", g.currentFunction, inst.Dst.Ident())
				g.variables.Loads[refname] = inst.Src
			default:
				ru = append(ru, g.storeRule(inst)...)
			}
		case *ir.InstFAdd:
			var r rules.Rule
			r = g.createInfixRule(inst.Ident(),
				inst.X.Ident(), inst.Y.Ident(), "+")
			g.tempRule(inst, r)
		case *ir.InstFSub:
			var r rules.Rule
			r = g.createInfixRule(inst.Ident(),
				inst.X.Ident(), inst.Y.Ident(), "-")
			g.tempRule(inst, r)
		case *ir.InstFMul:
			var r rules.Rule
			r = g.createInfixRule(inst.Ident(),
				inst.X.Ident(), inst.Y.Ident(), "*")
			g.tempRule(inst, r)
		case *ir.InstFDiv:
			var r rules.Rule
			r = g.createInfixRule(inst.Ident(),
				inst.X.Ident(), inst.Y.Ident(), "/")
			g.tempRule(inst, r)
		case *ir.InstFRem:
			//Cannot be implemented because SMT solvers do poorly with modulo
		case *ir.InstFCmp:
			var r rules.Rule
			op, y := g.createCompareRule(inst.Pred.String())
			if op == "true" || op == "false" {
				r = g.createInfixRule(inst.Ident(),
					inst.X.Ident(), y.(*rules.Wrap).Value, op)
			} else {
				r = g.createInfixRule(inst.Ident(),
					inst.X.Ident(), inst.Y.Ident(), op)
			}

			// If LLVM is storing this is a temp var
			// Happens in conditionals
			id := inst.Ident()
			if g.variables.IsTemp(id) {
				refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
				g.variables.Ref[refname] = r
				continue
			}

			ru = append(ru, r)
		case *ir.InstICmp:
			var r rules.Rule
			op, y := g.createCompareRule(inst.Pred.String())
			if op == "true" || op == "false" {
				r = g.createInfixRule(inst.Ident(),
					inst.X.Ident(), y.(*rules.Wrap).Value, op)
			} else {
				r = g.createInfixRule(inst.Ident(),
					inst.X.Ident(), inst.Y.Ident(), op)
			}

			id := inst.Ident()
			if g.variables.IsTemp(id) {
				refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
				g.variables.Ref[refname] = r
				continue
			}

			ru = append(ru, r)
		case *ir.InstCall:
			callee := inst.Callee.Ident()
			if g.isBuiltIn(callee) {
				meta := inst.Metadata // Is this in a "b || b" construction?
				if len(meta) > 0 {
					id := inst.Ident()
					refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
					inst.Metadata = nil // don't need this anymore
					g.variables.Loads[refname] = inst
				} else {
					r := g.parseBuiltIn(inst, false)
					ru = append(ru, r...)
				}
				continue
			}
			meta := inst.Metadata
			if g.isSameParallelGroup(meta) {
				g.localCallstack = append(g.localCallstack, callee)
			} else if g.singleParallelStep(callee) {
				r := g.executeCallstack()
				ru = append(ru, r...)

				r1 := g.generateFromCallstack([]string{callee})
				ru = append(ru, r1...)
			} else {
				r := g.executeCallstack()
				ru = append(ru, r...)

				g.localCallstack = append(g.localCallstack, callee)
			}
			g.updateParallelGroup(meta)
			g.returnVoid.Out()
		case *ir.InstXor:
			r := g.xorRule(inst)
			g.tempRule(inst, r)
		case *ir.InstAnd:
			if g.isStateChangeChain(inst) {
				sc := &rules.StateChange{
					Ors:  []value.Value{},
					Ands: []value.Value{},
				}
				andAd, _ := g.parseChoice(inst, sc)
				id := inst.Ident()
				refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
				g.variables.Loads[refname] = inst
				g.storedChoice[refname] = andAd

			} else {
				r := g.andRule(inst)
				g.tempRule(inst, r)
			}
		case *ir.InstOr:
			if g.isStateChangeChain(inst) {
				sc := &rules.StateChange{
					Ors:  []value.Value{},
					Ands: []value.Value{},
				}
				orAd, _ := g.parseChoice(inst, sc)
				id := inst.Ident()
				refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
				g.variables.Loads[refname] = inst
				g.storedChoice[refname] = orAd

			} else {
				r := g.orRule(inst)
				g.tempRule(inst, r)
			}
		case *ir.InstBitCast:
			//Do nothing
		default:
			panic(fmt.Sprintf("unrecognized instruction: %T", inst))

		}
	}
	return ru
}

func (g *Generator) parseTerms(terms []*ir.Block) ([]rules.Rule, []rules.Rule, *ir.Block) {
	var t, f []rules.Rule
	var a *ir.Block
	g.branchId = g.branchId + 1
	branch := fmt.Sprint("branch_", g.branchId)
	for _, term := range terms {
		bname := strings.Split(term.Ident(), "-")
		switch bname[len(bname)-1] {
		case "true":
			g.inPhiState.In()
			branchBlock := "true"
			t = g.parseBlock(term)

			t1 := g.executeCallstack()
			t = append(t, t1...)

			t = rules.TagRules(t, branch, branchBlock)
			g.inPhiState.Out()
		case "false":
			g.inPhiState.In()
			branchBlock := "false"
			f = g.parseBlock(term)

			g.localCallstack = []string{}
			f1 := g.executeCallstack()
			f = append(f, f1...)

			f = rules.TagRules(f, branch, branchBlock)
			g.inPhiState.Out()
		case "after":
			a = term
		default:
			panic(fmt.Sprintf("unrecognized terminal branch: %s", term.Ident()))
		}
	}

	return t, f, a
}

func (g *Generator) parseChoice(branch value.Value, sc *rules.StateChange) (*rules.StateChange, []value.Value) {
	var ret []value.Value
	switch branch := branch.(type) {
	case *ir.InstCall:
		return sc, append(ret, branch)
	case *ir.InstOr:
		refnamex := fmt.Sprintf("%s-%s", g.currentFunction, branch.X.Ident())
		vx := g.variables.Loads[refnamex]
		if g.peek(vx) != "infix" {
			sc, ret = g.parseChoice(vx, sc)
			sc.Ors = append(sc.Ors, ret...)
		} else {
			sc2 := g.storedChoice[refnamex]
			sc.Ands = append(sc.Ands, sc2.Ands...)
			sc.Ors = append(sc.Ors, sc2.Ors...)
		}
		delete(g.storedChoice, refnamex)

		refnamey := fmt.Sprintf("%s-%s", g.currentFunction, branch.Y.Ident())
		vy := g.variables.Loads[refnamey]
		if g.peek(vy) != "infix" {
			sc, ret = g.parseChoice(vy, sc)
			sc.Ors = append(sc.Ors, ret...)
		} else {
			sc2 := g.storedChoice[refnamey]
			sc.Ands = append(sc.Ands, sc2.Ands...)
			sc.Ors = append(sc.Ors, sc2.Ors...)
		}
		delete(g.storedChoice, refnamey)

		return sc, ret
	case *ir.InstAnd:
		refnamex := fmt.Sprintf("%s-%s", g.currentFunction, branch.X.Ident())
		vx := g.variables.Loads[refnamex]
		if g.peek(vx) != "infix" {
			sc, ret = g.parseChoice(vx, sc)
			sc.Ands = append(sc.Ands, ret...)
		} else {
			sc2 := g.storedChoice[refnamex]
			sc.Ands = append(sc.Ands, sc2.Ands...)
			sc.Ors = append(sc.Ors, sc2.Ors...)
		}
		delete(g.storedChoice, refnamex)

		refnamey := fmt.Sprintf("%s-%s", g.currentFunction, branch.Y.Ident())
		vy := g.variables.Loads[refnamey]
		if g.peek(vy) != "infix" {
			sc, ret = g.parseChoice(vy, sc)
			sc.Ands = append(sc.Ands, ret...)
		} else {
			sc2 := g.storedChoice[refnamey]
			sc.Ands = append(sc.Ands, sc2.Ands...)
			sc.Ors = append(sc.Ors, sc2.Ors...)
		}
		delete(g.storedChoice, refnamey)

		return sc, ret
	}
	return sc, ret
}

func (g *Generator) parseBuiltIn(call *ir.InstCall, complex bool) []rules.Rule {
	p := call.Args
	if len(p) == 0 {
		return []rules.Rule{}
	}

	bc, ok := p[0].(*ir.InstBitCast)
	if !ok {
		panic("improper argument to built in function")
	}

	id := bc.From.Ident()
	refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
	state := g.variables.Loads[refname]
	newState := state.Ident()
	base := newState[2 : len(newState)-1] //Because this is a charArray LLVM adds c"..." formatting we need to remove
	n := g.variables.SSA[base]
	prev := fmt.Sprintf("%s_%d", base, n)
	if !g.inPhiState.Check() {
		g.variables.NewPhi(base, n+1)
	} else {
		g.variables.StoreLastState(base, n+1)
	}
	g.addVarToRound(base, int(n+1))
	newState = g.variables.AdvanceSSA(base)
	g.AddNewVarChange(base, newState, prev)

	if complex {
		g.declareVar(newState, "Bool")
	}
	r1 := g.createRule(newState, "true", "Bool", "=")

	if g.currentFunction[len(g.currentFunction)-7:] != "__state" {
		panic("calling advance from outside the state chart")
	}

	base2 := g.currentFunction[1 : len(g.currentFunction)-7]
	n2 := g.variables.SSA[base2]
	prev2 := fmt.Sprintf("%s_%d", base2, n2)
	if !g.inPhiState.Check() {
		g.variables.NewPhi(base2, n2+1)
	} else {
		g.variables.StoreLastState(base2, n2+1)
	}

	g.addVarToRound(base2, int(n2+1))
	currentState := g.variables.AdvanceSSA(base2)
	g.AddNewVarChange(base2, currentState, prev2)
	if complex {
		g.declareVar(currentState, "Bool")
	}
	r2 := g.createRule(currentState, "false", "Bool", "=")
	return []rules.Rule{r1, r2}
}

func (g *Generator) isBuiltIn(c string) bool {
	if c == "@advance" || c == "@stay" {
		return true
	}
	return false
}

func (g *Generator) isBranchClosed(t []rules.Rule, f []rules.Rule) bool {
	if len(t) == 0 && len(f) == 0 {
		return true
	}
	return false
}

func (g *Generator) createRule(id string, val string, ty string, op string) rules.Rule {
	wid := &rules.Wrap{Value: id}
	wval := &rules.Wrap{Value: val}
	return &rules.Infix{X: wid, Ty: ty, Y: wval, Op: op}
}

func (g *Generator) createInfixRule(id string, x string, y string, op string) rules.Rule {
	x = g.convertInfixVar(x)
	y = g.convertInfixVar(y)

	refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
	g.variables.Ref[refname] = g.createRule(x, y, "", op)
	return g.variables.Ref[refname]
}

func (g *Generator) createCondRule(cond rules.Rule) rules.Rule {
	switch inst := cond.(type) {
	case *rules.Wrap:
		return inst
	case *rules.Infix:
		op, y := g.createCompareRule(inst.Op)
		inst.Op = op
		if op == "true" || op == "false" {
			inst.Y = y
		}
		return inst
	default:
		panic(fmt.Sprintf("Invalid conditional: %s", inst))
	}
}

func (g *Generator) createMultiCondRule(id string, x rules.Rule, y rules.Rule, op string) rules.Rule {
	refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
	g.variables.Ref[refname] = &rules.Infix{X: x, Ty: "Bool", Y: y, Op: op}
	return g.variables.Ref[refname]
}

func (g *Generator) createCompareRule(op string) (string, rules.Rule) {
	var y *rules.Wrap
	op = g.compareRuleOp(op)
	switch op {
	case "false":
		y = &rules.Wrap{Value: "False"}
	case "true":
		y = &rules.Wrap{Value: "True"}
	}
	return op, y
}

func (g *Generator) compareRuleOp(op string) string {
	switch op {
	case "false":
		return "false"
	case "oeq":
		return "="
	case "eq":
		return "="
	case "oge":
		return ">="
	case "ogt":
		return ">"
	case "ole":
		return "<="
	case "olt":
		return "<"
	case "one":
		return "!="
	case "ne":
		return "!="
	case "true":
		return "true"
	case "ueq":
		return "="
	case "uge":
		return ">="
	case "ugt":
		return ">"
	case "ule":
		return "<="
	case "ult":
		return "<"
	case "une":
		return "!="
	default:
		return op
	}
}

func (g *Generator) executeCallstack() []rules.Rule {
	stack := util.Copy(g.localCallstack)
	g.localCallstack = []string{}
	r := g.generateFromCallstack(stack)
	return r
}

func (g *Generator) peek(inst value.Value) string {
	switch inst.(type) {
	case *ir.InstOr, *ir.InstAnd:
		return "infix"
	case *ir.InstCall:
		return "call"
	default:
		panic("unsupported instruction type")
	}
}

func (g *Generator) isStateChangeChain(inst ir.Instruction) bool {
	switch inst := inst.(type) {
	case *ir.InstAnd:
		if !g.variables.IsTemp(inst.X.Ident()) {
			return false
		}

		switch inst.X.(type) {
		case *ir.InstCall, *ir.InstAnd, *ir.InstOr:
		default:
			return false
		}

		if !g.variables.IsTemp(inst.Y.Ident()) {
			return false
		}

		switch inst.Y.(type) {
		case *ir.InstCall, *ir.InstAnd, *ir.InstOr:
		default:
			return false
		}

	case *ir.InstOr:
		if !g.variables.IsTemp(inst.X.Ident()) {
			return false
		}

		switch inst.X.(type) {
		case *ir.InstCall, *ir.InstAnd, *ir.InstOr:
		default:
			return false
		}

		if !g.variables.IsTemp(inst.Y.Ident()) {
			return false
		}

		switch inst.Y.(type) {
		case *ir.InstCall, *ir.InstAnd, *ir.InstOr:
		default:
			return false
		}

	default:
		return false
	}
	return true
}

////////////////////////
// Some functions specific to variable names in rules
////////////////////////

func (g *Generator) AddNewVarChange(base string, id string, parent string) {
	var v *variables.VarChange
	if id == parent {
		v = &variables.VarChange{Id: id, Parent: ""}
	} else {
		v = &variables.VarChange{Id: id, Parent: parent}
	}

	if len(g.Results[base]) == 0 {
		g.Results[base] = append(g.Results[base], v)
	} else {
		g.Results[base] = append(g.Results[base], v)
	}
}

func (g *Generator) VarChangePhi(base string, end string, nums []int16) {
	for _, n := range nums {
		start := fmt.Sprintf("%s_%d", base, n)
		g.AddNewVarChange(base, end, start)
	}
}

func (g *Generator) tempToIdent(ru rules.Rule) rules.Rule {
	switch r := ru.(type) {
	case *rules.Wrap:
		return g.fetchIdent(r.Value, r)
	case *rules.Infix:
		r.X = g.tempToIdent(r.X)
		r.Y = g.tempToIdent(r.Y)
		return r
	}
	return ru
}

func (g *Generator) fetchIdent(id string, r rules.Rule) rules.Rule {
	if g.variables.IsTemp(id) {
		refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
		if v, ok := g.variables.Loads[refname]; ok {
			n := g.variables.SSA[id]
			if !g.inPhiState.Check() {
				g.variables.NewPhi(id, n+1)
			} else {
				g.variables.StoreLastState(id, n+1)
			}
			g.addVarToRound(id, int(n+1))
			id = g.variables.AdvanceSSA(v.Ident())
			wid := &rules.Wrap{Value: id}
			return wid
		} else if ref, ok := g.variables.Ref[refname]; ok {
			switch r := ref.(type) {
			case *rules.Infix:
				r.X = g.tempToIdent(r.X)
				r.Y = g.tempToIdent(r.Y)
				return r
			}
		} else {
			panic(fmt.Sprintf("smt generation error, value for %s not found", id))
		}
	}
	return r
}

func (g *Generator) convertInfixVar(x string) string {
	if g.variables.IsTemp(x) {
		refname := fmt.Sprintf("%s-%s", g.currentFunction, x)
		if v, ok := g.variables.Loads[refname]; ok {
			xid := v.Ident()
			xidNoPercent := g.variables.FormatIdent(xid)
			if g.parallelRunStart {
				n := g.variables.GetStartState(xidNoPercent)
				x = fmt.Sprintf("%s_%d", xidNoPercent, n)
				g.parallelRunStart = false
			} else {
				x = g.variables.GetSSA(xidNoPercent)
			}
		}
	}
	return x
}
func (g *Generator) isASolvable(id string) bool {
	id, _ = g.variables.GetVarBase(id)
	for _, v := range g.Unknowns {
		if v == id {
			return true
		}
	}
	for k := range g.Uncertains {
		if k == id {
			return true
		}
	}
	return false
}

func (g *Generator) allStateChangesInRule(ru rules.Rule) []string {
	var wg []string
	switch r := ru.(type) {
	case *rules.Infix:
		ch := g.allStateChangesInRule(r.X)
		wg = append(wg, ch...)
		ch = g.allStateChangesInRule(r.Y)
		wg = append(wg, ch...)

	case *rules.Ite:
		for _, w := range r.T {
			ch := g.allStateChangesInRule(w)
			wg = append(wg, ch...)
		}

		for _, w := range r.F {
			ch := g.allStateChangesInRule(w)
			wg = append(wg, ch...)
		}
	case *rules.WrapGroup:
		for _, w := range r.Wraps {
			ch := g.allStateChangesInRule(w)
			wg = append(wg, ch...)
		}
	case *rules.Wrap:
		if !g.variables.IsNumeric(r.Value) && !g.variables.IsBoolean(r.Value) { // Wraps might be static values
			return []string{r.Value}
		}
	case *rules.Ands:
		for _, w := range r.X {
			ch := g.allStateChangesInRule(w)
			wg = append(wg, ch...)
		}
	case *rules.Choices:
		for _, w := range r.X {
			ch := g.allStateChangesInRule(w)
			wg = append(wg, ch...)
		}
	}
	return wg
}

////////////////////////
// Rules to String
///////////////////////

func (g *Generator) writeAssertlessRule(op string, x string, y string) string {
	if y != "" {
		return fmt.Sprintf("(%s %s %s)", op, x, y)
	} else {
		return fmt.Sprintf("(%s %s)", op, x)
	}
}

func (g *Generator) writeBranch(ty string, cond string, t string, f string) string {
	return fmt.Sprintf("(%s %s %s %s)", ty, cond, t, f)
}

func (g *Generator) declareVar(id string, t string) {
	def := fmt.Sprintf("(declare-fun %s () %s)", id, t)
	g.inits = append(g.inits, def)
}

func (g *Generator) writeAssert(op string, stmt string) string {
	if op == "" {
		return fmt.Sprintf("(assert %s)", stmt)
	}
	return fmt.Sprintf("(assert (%s %s))", op, stmt)
}

func (g *Generator) writeBranchRule(r *rules.Infix) string {
	y := g.unpackRule(r.Y)
	x := g.unpackRule(r.X)

	return fmt.Sprintf("(%s %s %s)", r.Op, x, y)
}

func (g *Generator) writeRule(ru rules.Rule) string {
	switch r := ru.(type) {
	case *rules.Infix:
		y := g.unpackRule(r.Y)
		x := g.unpackRule(r.X)

		if y == "0x3DA3CA8CB153A753" { //An uncertain or unknown value
			g.declareVar(x, r.Ty)
			return ""
		}

		if r.Op == "or" {
			stmt := fmt.Sprintf("%s%s", x, y)
			return g.writeAssert("or", stmt)
		}

		if r.Op != "" && r.Op != "=" {
			return g.writeAssertlessRule(r.Op, x, y)
		}

		return g.writeInitRule(x, r.Ty, y)
	case *rules.Ite:
		cond := g.writeCond(r.Cond.(*rules.Infix))
		var tRule, fRule string
		var tEnds, fEnds []string
		for _, t := range r.T {
			tEnds = append(tEnds, g.writeBranchRule(t.(*rules.Infix)))
		}

		for _, f := range r.F {
			fEnds = append(fEnds, g.writeBranchRule(f.(*rules.Infix)))
		}

		if len(tEnds) > 1 {
			stmt := strings.Join(tEnds, " ")
			tRule = g.writeAssertlessRule("and", stmt, "")
		} else if len(tEnds) == 1 {
			tRule = tEnds[0]
		}

		if len(fEnds) > 1 {
			stmt := strings.Join(fEnds, " ")
			fRule = g.writeAssertlessRule("and", stmt, "")
		} else if len(fEnds) == 1 {
			fRule = fEnds[0]
		}

		br := g.writeBranch("ite", cond, tRule, fRule)
		return g.writeAssert("", br)
	case *rules.Wrap:
		return r.Value
	case *rules.Phi:
		g.declareVar(r.EndState, g.variables.LookupType(r.BaseVar, nil))
		ends := g.formatEnds(r.BaseVar, r.Nums, r.EndState)
		return g.writeAssert("or", ends)
	case *rules.Ands:
		var ands string
		for _, x := range r.X {
			var s string
			switch x := x.(type) {
			case *rules.Infix:
				s = g.writeBranchRule(x)
			default:
				s = g.writeRule(x)
			}
			ands = fmt.Sprintf("%s%s", ands, s)
		}
		return g.writeAssertlessRule("and", ands, "")
	case *rules.Choices:
		var ands string
		var s string
		for _, x := range r.X {
			s = g.writeRule(x)
			ands = fmt.Sprintf("%s%s", ands, s)
		}
		if r.Op == "or" {
			return g.writeAssert(r.Op, ands)
		}
		return g.writeAssert("", ands)
	default:
		panic(fmt.Sprintf("%T is not a valid rule type", r))
	}
}

func (g *Generator) writeCond(r *rules.Infix) string {
	y := g.unpackCondRule(r.Y)
	x := g.unpackCondRule(r.X)

	return g.writeAssertlessRule(r.Op, x, y)
}

func (g *Generator) unpackCondRule(x rules.Rule) string {
	switch r := x.(type) {
	case *rules.Wrap:
		return r.Value
	case *rules.Infix:
		x := g.unpackCondRule(r.X)
		y := g.unpackCondRule(r.Y)
		return g.writeAssertlessRule(r.Op, x, y)
	default:
		panic(fmt.Sprintf("%T is not a valid rule type", r))
	}
}

func (g *Generator) unpackRule(x rules.Rule) string {
	switch r := x.(type) {
	case *rules.Wrap:
		return r.Value
	case *rules.Infix:
		return g.writeRule(r)
	case *rules.Ands:
		return g.writeRule(r)
	case *rules.Choices:
		return g.writeRule(r)
	default:
		panic(fmt.Sprintf("%T is not a valid rule type", r))
	}
}

func (g *Generator) writeInitRule(id string, t string, val string) string {
	// Initialize: x = Int("x")
	g.declareVar(id, t)
	// Set rule: s.add(x == 2)
	return fmt.Sprintf("(assert (= %s %s))", id, val)
}

func (g *Generator) generateRules() []string {
	var rules []string
	for _, v := range g.rawRules {
		for _, ru := range v {
			rules = append(rules, g.writeRule(ru))
		}
	}
	return rules
}

////////////////////////////////////
// General rule store and load logic
///////////////////////////////////

func (g *Generator) constantRule(id string, c constant.Constant) string {
	switch val := c.(type) {
	case *constant.Float:
		ty := g.variables.LookupType(id, val)
		g.addVarToRound(id, 0)
		id = g.variables.AdvanceSSA(id)
		if g.isASolvable(id) {
			g.declareVar(id, ty)
		} else {
			v := val.X.String()
			if strings.Contains(v, ".") {
				return g.writeInitRule(id, ty, v)
			}
			return g.writeInitRule(id, ty, v+".0")
		}
	}
	return ""
}

func (g *Generator) loadsRule(inst *ir.InstLoad) {
	id := inst.Ident()
	refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
	g.variables.Loads[refname] = inst.Src
}

func (g *Generator) storeRule(inst *ir.InstStore) []rules.Rule {
	var ru []rules.Rule
	base := g.variables.FormatIdent(inst.Dst.Ident())
	if g.variables.IsTemp(inst.Src.Ident()) {
		srcId := inst.Src.Ident()
		refname := fmt.Sprintf("%s-%s", g.currentFunction, srcId)
		if val, ok := g.variables.Loads[refname]; ok {
			ty := g.variables.LookupType(refname, val)
			n := g.variables.SSA[base]
			prev := fmt.Sprintf("%s_%d", base, n)
			if !g.inPhiState.Check() {
				g.variables.NewPhi(base, n+1)
			} else {
				g.variables.StoreLastState(base, n+1)
			}
			id := g.variables.AdvanceSSA(base)
			g.addVarToRound(base, int(n+1))
			v := g.variables.FormatValue(val)
			if !g.variables.IsBoolean(v) && !g.variables.IsNumeric(v) {
				v = g.variables.FormatIdent(v)
				v = fmt.Sprintf("%s_%d", v, n)
			}
			g.AddNewVarChange(base, id, prev)
			ru = append(ru, g.createRule(id, v, ty, ""))
		} else if ref, ok := g.variables.Ref[refname]; ok {
			switch r := ref.(type) {
			case *rules.Infix:
				r.X = g.tempToIdent(r.X)
				r.Y = g.tempToIdent(r.Y)
				n := g.variables.SSA[base]
				prev := fmt.Sprintf("%s_%d", base, n)
				if !g.inPhiState.Check() {
					g.variables.NewPhi(base, n+1)
				} else {
					g.variables.StoreLastState(base, n+1)
				}
				id := g.variables.AdvanceSSA(base)
				g.addVarToRound(base, int(n+1))
				g.AddNewVarChange(base, id, prev)
				wid := &rules.Wrap{Value: id}
				if g.variables.IsBoolean(r.Y.String()) {
					ru = append(ru, &rules.Infix{X: wid, Ty: "Bool", Y: r, Op: "="})
				} else if g.isASolvable(r.X.String()) {
					ru = append(ru, &rules.Infix{X: wid, Ty: "Real", Y: r, Op: "="})
				} else {
					ru = append(ru, &rules.Infix{X: wid, Ty: "Real", Y: r})
				}
			default:
				n := g.variables.SSA[base]
				prev := fmt.Sprintf("%s_%d", base, n)
				if !g.inPhiState.Check() {
					g.variables.NewPhi(base, n+1)
				} else {
					g.variables.StoreLastState(base, n+1)
				}
				ty := g.variables.LookupType(base, nil)
				id := g.variables.AdvanceSSA(base)
				g.addVarToRound(base, int(n+1))
				g.AddNewVarChange(base, id, prev)
				wid := &rules.Wrap{Value: id}
				ru = append(ru, &rules.Infix{X: wid, Ty: ty, Y: r})
			}
		} else {
			panic(fmt.Sprintf("smt generation error, value for %s not found", base))
		}
	} else {
		ty := g.variables.LookupType(base, inst.Src)
		n := g.variables.SSA[base]
		prev := fmt.Sprintf("%s_%d", base, n)
		if !g.inPhiState.Check() {
			g.variables.NewPhi(base, n+1)
		} else {
			g.variables.StoreLastState(base, n+1)
		}
		id := g.variables.AdvanceSSA(base)
		g.addVarToRound(base, int(g.variables.SSA[base]))
		g.AddNewVarChange(base, id, prev)
		ru = append(ru, g.createRule(id, inst.Src.Ident(), ty, ""))
	}
	return ru
}

func (g *Generator) xorRule(inst *ir.InstXor) rules.Rule {
	id := inst.Ident()
	x := inst.X.Ident()
	xRule := g.variables.LookupCondPart(g.currentFunction, x)
	if xRule == nil {
		x = g.variables.ConvertIdent(g.currentFunction, x)
		xRule = &rules.Wrap{Value: x}
	}
	return g.createMultiCondRule(id, xRule, &rules.Wrap{}, "not")
}

func (g *Generator) andRule(inst *ir.InstAnd) rules.Rule {
	id := inst.Ident()
	x := inst.X.Ident()
	y := inst.Y.Ident()

	xRule := g.variables.LookupCondPart(g.currentFunction, x)
	if xRule == nil {
		x = g.variables.ConvertIdent(g.currentFunction, x)
		xRule = &rules.Wrap{Value: x}
	}

	yRule := g.variables.LookupCondPart(g.currentFunction, y)
	if yRule == nil {
		y = g.variables.ConvertIdent(g.currentFunction, y)
		yRule = &rules.Wrap{Value: y}
	}
	return g.createMultiCondRule(id, xRule, yRule, "and")
}

func (g *Generator) orRule(inst *ir.InstOr) rules.Rule {
	x := inst.X.Ident()
	y := inst.Y.Ident()
	id := inst.Ident()
	xRule := g.variables.LookupCondPart(g.currentFunction, x)
	if xRule == nil {
		x = g.variables.ConvertIdent(g.currentFunction, x)
		xRule = &rules.Wrap{Value: x}
	}

	yRule := g.variables.LookupCondPart(g.currentFunction, y)
	if yRule == nil {
		y = g.variables.ConvertIdent(g.currentFunction, y)
		yRule = &rules.Wrap{Value: y}
	}
	return g.createMultiCondRule(id, xRule, yRule, "or")
}

func (g *Generator) stateRules(key string, sc *rules.StateChange) rules.Rule {
	if len(sc.Ors) == 0 {
		and := g.andStateRule(key, sc.Ands)
		a := &rules.Ands{
			X: and,
		}

		c := &rules.Choices{
			X:  []*rules.Ands{a},
			Op: "and",
		}
		return c
	}

	and := g.andStateRule(key, sc.Ands)
	ors := g.orStateRule(key, sc.Ors)

	if len(sc.Ands) != 0 {
		ors["joined_ands"] = and
	}

	x := g.syncStateRules(ors)

	r := &rules.Choices{
		X:  x,
		Op: "or",
	}

	return r

}

func (g *Generator) orStateRule(choiceK string, choiceV []value.Value) map[string][]rules.Rule {
	g.inPhiState.In()

	and := make(map[string][]rules.Rule)
	for _, b := range choiceV {
		refname := fmt.Sprintf("%s-%s", g.currentFunction, b.Ident())
		and[refname] = g.parseBuiltIn(b.(*ir.InstCall), true)
	}
	delete(g.storedChoice, choiceK)

	g.inPhiState.Out()
	return and
}

func (g *Generator) andStateRule(andK string, andV []value.Value) []rules.Rule {
	g.inPhiState.In()

	var ands []rules.Rule
	for _, b := range andV {
		a := g.parseBuiltIn(b.(*ir.InstCall), true)
		ands = append(ands, a...)
	}
	delete(g.storedChoice, andK)

	g.inPhiState.Out()
	return ands
}

func (g *Generator) syncStateRules(branches map[string][]rules.Rule) []*rules.Ands {
	g.inPhiState.In()
	g.newFork()

	var e []rules.Rule
	var keys []string
	ends := make(map[string][]rules.Rule)
	phis := make(map[string]int16)
	var x []*rules.Ands

	for k, v := range branches {
		keys = append(keys, k)
		g.buildForkChoice(v, k)
		e, phis = g.capCond(k, phis)
		ends[k] = append(v, e...)
	}

	syncs := g.capCondSyncRules(keys)
	for k, v := range syncs {
		e2 := append(ends[k], v...)
		a := &rules.Ands{
			X: e2,
		}
		x = append(x, a)
	}
	g.inPhiState.Out()
	return x
}

func (g *Generator) tempRule(inst value.Value, r rules.Rule) {
	// If infix rule is stored in a temp variable
	id := inst.Ident()
	if g.variables.IsTemp(id) {
		refname := fmt.Sprintf("%s-%s", g.currentFunction, id)
		g.variables.Ref[refname] = r
	}
}

////////////////////////
// Generating SMT
///////////////////////

func (g *Generator) SMT() string {
	var out bytes.Buffer

	out.WriteString("(set-logic QF_NRA)")
	out.WriteString(strings.Join(g.inits, "\n"))
	out.WriteString(strings.Join(g.constants, "\n"))
	out.WriteString(strings.Join(g.rules, "\n"))
	out.WriteString(strings.Join(g.asserts, "\n"))

	return out.String()
}

///////////////////////////////
// Logic Behind Parallel Runs
//////////////////////////////

func (g *Generator) parallelPermutations(p []string) (permuts [][]string) {
	var rc func([]string, int)
	rc = func(a []string, k int) {
		if k == len(a) {
			permuts = append(permuts, append([]string{}, a...))
		} else {
			for i := k; i < len(p); i++ {
				a[k], a[i] = a[i], a[k]
				rc(a, k+1)
				a[k], a[i] = a[i], a[k]
			}
		}
	}
	rc(p, 0)

	return permuts
}

func (g *Generator) runParallel(perm [][]string) []rules.Rule {
	var ru []rules.Rule
	g.branchId = g.branchId + 1
	branch := fmt.Sprint("branch_", g.branchId)
	g.newFork()
	for i, calls := range perm {
		branchBlock := fmt.Sprint("option_", i)
		var opts [][]rules.Rule
		varState := g.variables.SaveState()
		for _, c := range calls {
			g.parallelRunStart = true
			g.inPhiState.Out() //Don't behave like we're in Phi inside the function
			v := g.functions[c]
			raw := g.parseFunction(v)
			g.inPhiState.In()
			raw = rules.TagRules(raw, branch, branchBlock)
			opts = append(opts, raw)
		}
		//Flat the rules
		raw := g.parallelRules(opts)
		// Pull all the variables out of the rules and
		// sort them into fork choices
		g.buildForkChoice(raw, "")
		g.variables.LoadState(varState)
		ru = append(ru, raw...)
	}

	ru = append(ru, g.capParallel()...)
	return ru
}

func (g *Generator) parallelRules(r [][]rules.Rule) []rules.Rule {
	var rules []rules.Rule
	for _, op := range r {
		rules = append(rules, op...) // Flatten
	}
	return rules
}

func (g *Generator) isSameParallelGroup(meta ir.Metadata) bool {
	for _, v := range meta {

		if v.Name == g.parallelGrouping {
			return true
		}

		if g.parallelGrouping == "" {
			return true
		}
	}

	return false
}

func (g *Generator) singleParallelStep(callee string) bool {
	if len(g.localCallstack) == 0 {
		return false
	}

	if callee == g.localCallstack[len(g.localCallstack)-1] {
		return true
	}

	return false
}

func (g *Generator) updateParallelGroup(meta ir.Metadata) {
	for _, v := range meta {
		if v.Name[0:5] != "round-" {
			g.parallelGrouping = v.Name
		}
	}
}

func (g *Generator) capParallel() []rules.Rule {
	// Take all the end variables for the all the branches
	// and cap them with a phi value
	// writes OR nodes to end each parallel run

	fork := g.getCurrentFork()
	var ru []rules.Rule
	for k, v := range fork {
		id := g.variables.AdvanceSSA(k)
		g.addVarToRound(k, int(g.variables.SSA[k]))

		var nums []int16
		for _, c := range v {
			nums = append(nums, c.GetEnd())
		}

		rule := &rules.Phi{
			BaseVar:  k,
			EndState: id,
			Nums:     nums,
		}
		g.VarChangePhi(k, id, nums)
		ru = append(ru, rule)

		base, i := g.variables.GetVarBase(id)
		n := int16(i)
		if g.inPhiState.Level() == 1 {
			g.variables.NewPhi(base, n)
		} else {
			g.variables.StoreLastState(base, n)
		}

	}
	return ru
}

func (g *Generator) capRule(k string, nums []int16, id string) []rules.Rule {
	var e []rules.Rule
	for _, v := range nums {
		id2 := fmt.Sprint(k, "_", v)
		g.AddNewVarChange(k, id, id2)
		ty := g.variables.LookupType(k, nil)
		if ty == "Bool" {
			r := &rules.Infix{
				X:  &rules.Wrap{Value: id},
				Y:  &rules.Wrap{Value: id2},
				Op: "=",
				Ty: "Bool",
			}
			e = append(e, r)
		} else {
			r := &rules.Infix{
				X:  &rules.Wrap{Value: id},
				Y:  &rules.Wrap{Value: id2},
				Op: "=",
				Ty: "Real",
			}
			e = append(e, r)
		}
	}
	return e
}

func (g *Generator) capCond(b string, phis map[string]int16) ([]rules.Rule, map[string]int16) {
	fork := g.getCurrentFork()
	var rules []rules.Rule
	for k, v := range fork {
		// Because we're looking at all the variables in
		// the true branch THEN all the variables in the
		// false branch, we only increment the variable
		// when we produce the phi value for the first time
		var id string
		if phi, ok := phis[k]; !ok {
			id = g.variables.AdvanceSSA(k)
			g.declareVar(id, g.variables.LookupType(k, nil))
			_, i := g.variables.GetVarBase(id)
			g.addVarToRound(k, i)
			phis[k] = int16(i)
		} else {
			id = fmt.Sprintf("%s_%d", k, phi)
		}

		for _, c := range v {
			if c.Branch == b {
				rules = append(rules, g.capRule(k, []int16{c.GetEnd()}, id)...)
			}
		}
	}
	return rules, phis
}

func (g *Generator) capCondSyncRules(branches []string) map[string][]rules.Rule {
	// For cases where variables changed in one branch are not
	// present in the other, add a rule
	ends := make(map[string][]rules.Rule)
	for _, b := range branches {
		var e []rules.Rule
		fork := g.getCurrentFork()
		for k, c := range fork {
			if len(c) == 1 && c[0].Branch == b {
				start := g.variables.GetStartState(k)
				id := g.variables.GetSSA(k)
				e = append(e, g.capRule(k, []int16{start}, id)...)
				n := g.variables.SSA[k]
				if g.inPhiState.Level() == 1 {
					g.variables.NewPhi(k, n)
				} else {
					g.variables.StoreLastState(k, n)
				}
			}
		}
		for _, notB := range util.Intersection(branches, []string{b}, true) {
			if _, ok := ends[notB]; !ok {
				ends[notB] = e
			} else {
				ends[notB] = append(ends[notB], e...)
			}
		}
	}
	return ends
}

func (g *Generator) formatEnds(k string, nums []int16, id string) string {
	var e []string
	for _, v := range nums {
		v := fmt.Sprint(k, "_", strconv.Itoa(int(v)))
		r := g.writeAssertlessRule("=", id, v)
		e = append(e, r)
	}
	return strings.Join(e, " ")
}

////////////////////////
// Temporal Logic
///////////////////////

func (g *Generator) applyTemporalLogic(temp string, ir []string, temporalFilter string, on string, off string) string {
	switch temp {
	case "eventually":
		if len(ir) > 1 {
			or := fmt.Sprintf("(%s %s)", on, strings.Join(ir, " "))
			return or
		}
		return ir[0]
	case "always":
		if len(ir) > 1 {
			or := fmt.Sprintf("(%s %s)", off, strings.Join(ir, " "))
			return or
		}
		return ir[0]
	case "eventually-always":
		if len(ir) > 1 {
			or := g.eventuallyAlways(ir)
			return or
		}
		return ir[0]
	default:
		if len(ir) > 1 {
			var op string
			switch temporalFilter {
			case "nft":
				op = "or"
			case "nmt":
				op = "or"
			default:
				op = off
			}
			or := fmt.Sprintf("(%s %s)", op, strings.Join(ir, " "))
			return or
		}
		return ir[0]
	}
}

func (g *Generator) eventuallyAlways(ir []string) string {
	var progression []string
	for i := range ir {
		s := fmt.Sprintf("(and %s)", strings.Join(ir[i:], " "))
		progression = append(progression, s)
	}
	return fmt.Sprintf("(or %s)", strings.Join(progression, " "))
}
