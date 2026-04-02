/-
  FaultSemantics.Execution

  Phase 3: Statement execution, round semantics, and parallel composition.
  Builds on the LTS transition relation to define how complete Fault
  programs execute over bounded rounds.
-/
import FaultSemantics.LTS

open Cslib

/-! ## Statement Execution (Relational)

  ExecStmt and ExecStmts are mutually inductive: a single statement
  may contain a block (ifThenElse, seq, parallel), and a block is
  a list of statements. -/

mutual

/-- Execute a single statement, relating input state to output state and trace.
    Uses `EvalR` for expression evaluation so unknown/uncertain values
    create nondeterministic executions (matching SMT solver behavior). -/
inductive ExecStmt : FaultState → Stmt → List Label → FaultState → Prop where
  /-- Flow assignment (nondeterministic via EvalR for unknowns) -/
  | flowAssign (σ : FaultState) (x : Name) (op : FlowOp) (e : Expr) (v : SVal) :
      EvalR σ e v →
      ExecStmt σ (.flowAssign x op e)
        [.assign x op v]
        (σ.setVar x (applyFlowOp op (σ.getVar x) v))

  /-- Conditional: true branch (nondeterministic via EvalR) -/
  | ifTrue (σ σ' : FaultState) (cond : Expr) (thenBody elseBody : List Stmt)
      (μs : List Label) :
      EvalR σ cond (.bool true) →
      ExecStmts σ thenBody μs σ' →
      ExecStmt σ (.ifThenElse cond thenBody elseBody) (.branch true :: μs) σ'

  /-- Conditional: false branch (nondeterministic via EvalR) -/
  | ifFalse (σ σ' : FaultState) (cond : Expr) (thenBody elseBody : List Stmt)
      (μs : List Label) :
      EvalR σ cond (.bool false) →
      ExecStmts σ elseBody μs σ' →
      ExecStmt σ (.ifThenElse cond thenBody elseBody) (.branch false :: μs) σ'

  /-- Call a named function (body resolved externally, passed as parameter) -/
  | call (σ σ' : FaultState) (funcName : Name) (body : List Stmt) (μs : List Label) :
      ExecStmts σ body μs σ' →
      ExecStmt σ (.call funcName) (.flowExec funcName funcName :: μs) σ'

  /-- Advance component state -/
  | advance (σ : FaultState) (target : Name) (comp newState : Name) :
      ExecStmt σ (.advance target)
        [.stateEntry comp newState]
        (σ.setCompState comp newState)

  /-- Stay: no-op -/
  | stay (σ : FaultState) :
      ExecStmt σ .stay [.tau] σ

  /-- Sequential block -/
  | seq (σ σ' : FaultState) (stmts : List Stmt) (μs : List Label) :
      ExecStmts σ stmts μs σ' →
      ExecStmt σ (.seq stmts) μs σ'

  /-- Parallel: choose a permutation (nondeterministic interleaving) -/
  | parallel (σ σ' : FaultState) (stmts perm : List Stmt) (μs : List Label) :
      perm.Perm stmts →
      ExecStmts σ perm μs σ' →
      ExecStmt σ (.parallel stmts) μs σ'

/-- Execute a list of statements sequentially -/
inductive ExecStmts : FaultState → List Stmt → List Label → FaultState → Prop where
  /-- Empty statement list -/
  | nil (σ : FaultState) :
      ExecStmts σ [] [] σ

  /-- Execute head, then tail -/
  | cons (σ σ_mid σ' : FaultState) (s : Stmt) (ss : List Stmt)
      (μs₁ μs₂ : List Label) :
      ExecStmt σ s μs₁ σ_mid →
      ExecStmts σ_mid ss μs₂ σ' →
      ExecStmts σ (s :: ss) (μs₁ ++ μs₂) σ'

end

/-! ## Flow Function Resolution -/

/-- Look up a flow function body by name in a spec -/
def resolveFlowFunc (spec : Spec) (flowName funcName : Name) : Option (List Stmt) :=
  spec.flows.findSome? fun fl =>
    if fl.name == flowName then
      (fl.funcs.find? fun (n, _) => n == funcName) |>.map (·.2)
    else none

/-- Look up a component state function body -/
def resolveStateFunc (comps : List CompDef) (compName stateName : Name) : Option (List Stmt) :=
  comps.findSome? fun c =>
    if c.name == compName then
      (c.states.find? fun (n, _) => n == stateName) |>.map (·.2)
    else none

/-! ## Round Execution -/

/-- Execute one round of a spec's run block -/
inductive ExecRound :
    FaultState → List Stmt → List Name → List Label → FaultState → Prop where
  | mk (σ σ_run : FaultState) (runBody : List Stmt) (vars : List Name)
      (μs_run : List Label) :
      ExecStmts σ runBody μs_run σ_run →
      ExecRound σ runBody vars
        (μs_run ++ [.round σ.round])
        ((σ_run.snapshot vars).nextRound)

/-- Execute N rounds of a spec -/
inductive ExecRounds :
    FaultState → Nat → List Stmt → List Name → List Label → FaultState → Prop where
  | zero (σ : FaultState) (runBody : List Stmt) (vars : List Name) :
      ExecRounds σ 0 runBody vars [] σ

  | succ (σ σ_mid σ' : FaultState) (n : Nat) (runBody : List Stmt) (vars : List Name)
      (μs₁ μs₂ : List Label) :
      ExecRound σ runBody vars μs₁ σ_mid →
      ExecRounds σ_mid n runBody vars μs₂ σ' →
      ExecRounds σ (n + 1) runBody vars (μs₁ ++ μs₂) σ'

/-! ## System-Level Round Execution (with Components) -/

/-- Execute component state functions for all active components in a round -/
inductive ExecComponents :
    FaultState → List CompDef → List Label → FaultState → Prop where
  | nil (σ : FaultState) :
      ExecComponents σ [] [] σ

  | cons (σ σ_mid σ' : FaultState) (comp : CompDef) (rest : List CompDef)
      (body : List Stmt) (μs₁ μs₂ : List Label) :
      (comp.states.find? fun (n, _) => n == σ.compState comp.name)
        = some (σ.compState comp.name, body) →
      ExecStmts σ body μs₁ σ_mid →
      ExecComponents σ_mid rest μs₂ σ' →
      ExecComponents σ (comp :: rest) (μs₁ ++ μs₂) σ'

  /-- Component has no matching state function (skip) -/
  | skip (σ σ' : FaultState) (comp : CompDef) (rest : List CompDef)
      (μs : List Label) :
      (comp.states.find? fun (n, _) => n == σ.compState comp.name) = none →
      ExecComponents σ rest μs σ' →
      ExecComponents σ (comp :: rest) μs σ'

/-- A full system round: run block + component state functions + snapshot -/
inductive ExecSystemRound :
    FaultState → List Stmt → List CompDef → List Name → List Label → FaultState → Prop where
  | mk (σ σ_run σ_comp : FaultState) (runBody : List Stmt)
      (comps : List CompDef) (vars : List Name)
      (μs_run μs_comp : List Label) :
      ExecStmts σ runBody μs_run σ_run →
      ExecComponents σ_run comps μs_comp σ_comp →
      ExecSystemRound σ runBody comps vars
        (μs_run ++ μs_comp ++ [.round σ.round])
        ((σ_comp.snapshot vars).nextRound)

/-! ## Full Program Execution (Phase 8.2: Init Blocks)

  The Go compiler executes `for N init{...} run{...}` as:
  1. Execute init block ONCE (round 0)
  2. Execute run block N times (rounds 0..N-1)

  This matches llvm/compiler.go:359-376:
    if i == 0 { compileBlock(v.Inits) }
    compileBlock(v.Body)
-/

/-- Execute a complete program: init once, then N rounds of run -/
inductive ExecProgram :
    FaultState → List Stmt → List Stmt → Nat → List Name →
    List Label → FaultState → Prop where
  | mk (σ σ_init σ' : FaultState) (initBlock runBlock : List Stmt)
      (n : Nat) (vars : List Name) (μs_init μs_rounds : List Label) :
      -- 1. Execute init block once
      ExecStmts σ initBlock μs_init σ_init →
      -- 2. Execute N rounds of the run block
      ExecRounds σ_init n runBlock vars μs_rounds σ' →
      ExecProgram σ initBlock runBlock n vars (μs_init ++ μs_rounds) σ'

/-- Execute N system rounds (with components) -/
inductive ExecSystemRounds :
    FaultState → Nat → List Stmt → List CompDef → List Name →
    List Label → FaultState → Prop where
  | zero (σ : FaultState) (runBody : List Stmt) (comps : List CompDef)
      (vars : List Name) :
      ExecSystemRounds σ 0 runBody comps vars [] σ

  | succ (σ σ_mid σ' : FaultState) (n : Nat) (runBody : List Stmt)
      (comps : List CompDef) (vars : List Name) (μs₁ μs₂ : List Label) :
      ExecSystemRound σ runBody comps vars μs₁ σ_mid →
      ExecSystemRounds σ_mid n runBody comps vars μs₂ σ' →
      ExecSystemRounds σ (n + 1) runBody comps vars (μs₁ ++ μs₂) σ'

/-- Execute a complete system program: init once, then N rounds with components -/
inductive ExecSystemProgram :
    FaultState → List Stmt → List Stmt → List CompDef → Nat → List Name →
    List Label → FaultState → Prop where
  | mk (σ σ_init σ' : FaultState) (initBlock runBlock : List Stmt)
      (comps : List CompDef) (n : Nat) (vars : List Name)
      (μs_init : List Label) (μs_rounds : List Label) :
      -- 1. Execute init block once
      ExecStmts σ initBlock μs_init σ_init →
      -- 2. Execute N system rounds (run + components)
      ExecSystemRounds σ_init n runBlock comps vars μs_rounds σ' →
      ExecSystemProgram σ initBlock runBlock comps n vars
        (μs_init ++ μs_rounds) σ'
