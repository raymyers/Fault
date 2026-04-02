# Implementing the Fault Language from Formal Semantics

This guide describes how to build a correct implementation of the
[Fault](https://github.com/Fault-lang/Fault) modeling language using the
Lean 4 formalization in `semantics/FaultSemantics/`. The guide is
language-agnostic — it describes the data structures, algorithms, and rules
your implementation must follow.

The formalization is the source of truth. File references like `Syntax.lean:15`
point to the Lean source where the formal definition lives.

---

## Table of Contents

1. [Overview](#1-overview)
2. [Parsing to AST](#2-parsing-to-ast)
3. [Name Resolution](#3-name-resolution)
4. [Building the Initial State](#4-building-the-initial-state)
5. [Expression Evaluation](#5-expression-evaluation)
6. [Statement Execution](#6-statement-execution)
7. [Round Execution](#7-round-execution)
8. [Program Execution](#8-program-execution)
9. [Assertions and Model Checking](#9-assertions-and-model-checking)
10. [SMT Encoding](#10-smt-encoding)
11. [Nondeterminism and Unknowns](#11-nondeterminism-and-unknowns)
12. [Testing Against the Reference](#12-testing-against-the-reference)

---

## 1. Overview

Fault is a **bounded model checking** language for system dynamics. A Fault
program defines stocks (state variables), flows (state transitions), and
components (state machines). The compiler translates the program into SMT
constraints and asks a solver (Z3) to find counterexamples to assertions.

The execution model is:

```
Parse → Resolve Names → Build Initial State → Execute (N rounds) → Check Assertions
```

There are two file types:
- **`.fspec`** — a specification: stocks, flows, constants, assertions, run block
- **`.fsystem`** — a system: imports `.fspec` files, adds components (state machines)

Formal definitions: `Spec`, `System` (`Syntax.lean:128-139`)

---

## 2. Parsing to AST

Your parser must produce the types defined in `Syntax.lean`. The ANTLR4
grammar files in the reference compiler (`grammar/FaultLexer.g4`,
`grammar/FaultParser.g4`) define the concrete syntax.

### Values (`Syntax.lean:15`)

```
Val = Nat(n)                    -- integer literal (treated as real)
    | Float(f)                  -- floating-point literal
    | Bool(b)                   -- true / false
    | Str(s)                    -- string literal (compiles to boolean false)
    | Unknown                   -- solver-determined free variable
    | Uncertain(mean, sigma)    -- normally distributed free variable
    | Nil
```

### Expressions (`Syntax.lean:51`)

```
Expr = Lit(val)                 -- literal value
     | Var(name)                -- variable reference
     | BinOp(op, left, right)   -- binary operation
     | UnOp(op, expr)           -- unary operation
     | Dot(expr, field)         -- property access (resolved before execution)
     | History(name, offset)    -- temporal reference: name[now + offset]
     | Choose(exprs)            -- nondeterministic choice (||)
```

### Statements (`Syntax.lean:64`)

```
Stmt = FlowAssign(name, op, expr)      -- stock op= expr
     | IfThenElse(cond, then, else)    -- conditional
     | Call(funcName)                    -- invoke a flow function
     | Advance(target)                  -- state machine transition
     | Stay                             -- remain in current state
     | Seq(stmts)                       -- sequential block
     | Parallel(stmts)                  -- concurrent block (|)
```

### Flow Operators (`Syntax.lean:42`)

| Syntax | FlowOp  | Meaning                        |
|--------|---------|--------------------------------|
| `=`    | Assign  | Replace: `stock := expr`       |
| `<-`   | Inflow  | Increment: `stock += expr`     |
| `->`   | Outflow | Decrement: `stock -= expr`     |

### Binary Operators (`Syntax.lean:28`)

Arithmetic: `add`, `sub`, `mul`, `div`, `mod`, `exp`
Comparison: `eq`, `neq`, `lt`, `le`, `gt`, `ge`
Logical: `and`, `or`
Bitwise: `lshift`, `rshift`, `bitAnd`, `bitOr`, `bitXor`, `bitClear`

### Temporal Modalities (`Syntax.lean:77`)

```
Temporal = Always              -- holds at every round (default)
         | Eventually          -- holds at some round
         | EventuallyAlways    -- once true, stays true
         | Nmt(n)              -- true no more than n times
         | Nft(n)              -- true no fewer than n times
```

### Invariants (`Syntax.lean:88`)

```
Invariant = Assert(expr, temporal)
          | Assume(expr, temporal)
          | AssertWhen(guard, body, temporal)    -- conditional assertion
          | AssumeWhen(guard, body, temporal)    -- conditional assumption
```

---

## 3. Name Resolution

**Before execution, all names must be flattened to underscore-delimited
strings.** This eliminates `Expr.Dot` nodes from the AST.

Formal definitions: `Resolve.lean`

### 3.1 Flattening (`Resolve.lean:21`)

Join name parts with underscores:
```
flattenName(["myspec", "flow1", "vault", "value"]) = "myspec_flow1_vault_value"
```

Every qualified reference like `flow1.vault.value` in spec `myspec` becomes
the flat string `myspec_flow1_vault_value`.

### 3.2 Scope Context

When processing an identifier, prepend the current scope:
```
context = [specName] ++ scopeParts
qualified = context ++ identifierParts
flat = flattenName(qualified)
```

For example, inside spec `"battery"`, flow `"life"`, the reference
`capacity.time` resolves to `flattenName(["battery", "life", "capacity", "time"])
= "battery_life_capacity_time"`.

### 3.3 Alias Resolution (Stock Swaps) (`Resolve.lean:49`)

Swaps create name aliases. When `flow.target = newStock`, an alias maps
the old flat name to the new flat name. Resolution is **recursive**:

```
resolveAlias(aliases, name):
    if aliases[name] exists:
        return resolveAlias(aliases, aliases[name])
    else:
        return name
```

Use a recursion limit to prevent infinite loops on circular aliases.

### 3.4 Expression Resolution (`Resolve.lean:68`)

Walk the AST and replace every `Dot(base, field)` with `Var(flatName)`:

```
resolveExpr(aliases, scope, Dot(e, field)):
    base = resolveExpr(aliases, scope, e)
    if base is Var(x):
        return Var(resolveAlias(aliases, x + "_" + field))
    else:
        return Var(resolveAlias(aliases, flattenName(scope ++ [field])))
```

Apply `resolveExpr` to all expressions in statements, invariants, etc.

### 3.5 Import Resolution (`Resolve.lean:108`)

For `.fsystem` files that import `.fspec` files:
- Merge all stocks, flows, and constants from imported specs
- Keep invariants (assertions and assumptions) from imported specs
- Ignore run blocks from imported specs
- The system's own components and run block are primary

Build a `ResolvedProgram` (`Resolve.lean:158`) containing the merged result.

### 3.6 Component Validation (`Resolve.lean:134`)

Component state functions must NOT contain direct `FlowAssign` statements.
They may only contain: `Advance`, `Stay`, `Call`, `IfThenElse`, `Seq`, `Parallel`.

---

## 4. Building the Initial State

Formal definition: `FaultState` (`State.lean:35`)

The runtime state has four components:

```
FaultState:
    env       : Name → SVal      -- variable values
    round     : Nat               -- current round number (0-indexed)
    compState : Name → Name       -- component → current state name
    history   : Name → Nat → SVal -- variable → round → historical value
```

### 4.1 Semantic Values (`State.lean:14`)

Runtime values are simplified from AST values:

```
SVal = Real(f)      -- all numerics become reals
     | Bool(b)      -- booleans
     | Nil           -- undefined / error
```

### 4.2 Initialization (`State.lean:98`)

Build the initial state from stock definitions and constants:

```
for each stock in program.stocks:
    for each (propName, val) in stock.props:
        env[propName] = toSVal(val)

for each constant in program.constants:
    env[constant.name] = toSVal(constant.value)

round = 0

for each (compName, stateName) in program.startStates:
    compState[compName] = stateName

history = everywhere Nil
```

Value conversion:
- `Val.Nat(n)` → `SVal.Real(float(n))`
- `Val.Float(f)` → `SVal.Real(f)`
- `Val.Bool(b)` → `SVal.Bool(b)`
- `Val.Str(s)` → `SVal.Bool(false)` (strings compile to false)
- `Val.Unknown` → depends on execution mode (see Section 11)
- `Val.Uncertain(μ, σ)` → depends on execution mode (see Section 11)

---

## 5. Expression Evaluation

Formal definition: `eval` (`LTS.lean:48`), `EvalR` (`LTS.lean:74`)

### 5.1 Deterministic Evaluation

For concrete values (no unknowns/uncertains), evaluation is a pure function:

```
eval(state, Lit(Nat(n)))       = Real(float(n))
eval(state, Lit(Float(f)))     = Real(f)
eval(state, Lit(Bool(b)))      = Bool(b)
eval(state, Lit(Str(s)))       = Bool(false)
eval(state, Lit(Unknown))      = Nil
eval(state, Lit(Uncertain(…))) = Nil
eval(state, Var(x))            = state.env[x]
eval(state, BinOp(op, l, r))  = evalBinOp(op, eval(state, l), eval(state, r))
eval(state, UnOp(op, e))      = evalUnOp(op, eval(state, e))
eval(state, Dot(e, _))        = eval(state, e)     -- should be resolved away
eval(state, History(x, k))    = state.history[x][state.round + k]
eval(state, Choose(_))        = Nil                 -- nondeterministic
```

### 5.2 Binary Operations (`LTS.lean:15`)

| Op    | Real × Real | Bool × Bool | Otherwise |
|-------|-------------|-------------|-----------|
| `add` | `a + b`     | —           | Nil       |
| `sub` | `a - b`     | —           | Nil       |
| `mul` | `a * b`     | —           | Nil       |
| `div` | `a / b`     | —           | Nil       |
| `eq`  | `a == b`    | `a == b`    | Nil       |
| `neq` | `a != b`    | `a != b`    | Nil       |
| `lt`  | `a < b`     | —           | Nil       |
| `le`  | `a <= b`    | —           | Nil       |
| `gt`  | `a > b`     | —           | Nil       |
| `ge`  | `a >= b`    | —           | Nil       |
| `and` | —           | `a && b`    | Nil       |
| `or`  | —           | `a ∣∣ b`   | Nil       |

### 5.3 Unary Operations (`LTS.lean:38`)

| Op    | Real       | Bool       | Otherwise |
|-------|-----------|------------|-----------|
| `neg` | `-a`      | —          | Nil       |
| `not` | —         | `!a`       | Nil       |

### 5.4 Flow Operations (`LTS.lean:159`)

```
applyFlowOp(Assign,  current, new)  = new
applyFlowOp(Inflow,  Real(a), Real(b)) = Real(a + b)
applyFlowOp(Outflow, Real(a), Real(b)) = Real(a - b)
applyFlowOp(Inflow,  _,       new)  = new     -- fallback
applyFlowOp(Outflow, _,       new)  = new     -- fallback
```

---

## 6. Statement Execution

Formal definition: `ExecStmt` (`Execution.lean:23`)

Each statement transforms a state and produces a trace of labels.

### 6.1 Flow Assignment

```
FlowAssign(x, op, expr):
    v = eval(state, expr)
    current = state.env[x]
    state' = state with env[x] = applyFlowOp(op, current, v)
    trace = [Assign(x, op, v)]
```

### 6.2 Conditional

```
IfThenElse(cond, thenBody, elseBody):
    if eval(state, cond) == Bool(true):
        (state', trace) = execStmts(state, thenBody)
        return (state', [Branch(true)] ++ trace)
    else if eval(state, cond) == Bool(false):
        (state', trace) = execStmts(state, elseBody)
        return (state', [Branch(false)] ++ trace)
```

For model checking with unknowns, BOTH branches must be explored
(see Section 11).

### 6.3 Function Call

```
Call(funcName):
    body = lookupFlowFunc(funcName)
    (state', trace) = execStmts(state, body)
    return (state', [FlowExec(funcName)] ++ trace)
```

### 6.4 State Machine Transitions

```
Advance(target):
    (comp, newState) = parseTarget(target)
    state' = state with compState[comp] = newState
    trace = [StateEntry(comp, newState)]

Stay:
    state' = state      -- no change
    trace = [Tau]
```

`advance(this.open)` sets the current component to state `open`.
The new state is NOT entered until the next round.

### 6.5 Sequential Composition

```
Seq([s1, s2, …, sn]):
    (state1, trace1) = execStmt(state, s1)
    (state2, trace2) = execStmt(state1, s2)
    …
    return (stateN, trace1 ++ trace2 ++ … ++ traceN)
```

### 6.6 Parallel Composition (`|` operator)

```
Parallel([s1, s2, …, sn]):
    pick ANY permutation perm of [s1, …, sn]
    (state', trace) = execStmts(state, perm)
    return (state', trace)
```

Every permutation is a valid execution. For model checking, you must
consider ALL permutations (the SMT solver picks the one that produces
a counterexample).

---

## 7. Round Execution

### 7.1 Single Round (spec only) (`Execution.lean:105`)

```
execRound(state, runBody, vars):
    (state_run, trace_run) = execStmts(state, runBody)
    state_snap = snapshot(state_run, vars)
    state_next = nextRound(state_snap)
    return (state_next, trace_run ++ [Round(state.round)])
```

### 7.2 Single System Round (with components) (`Execution.lean:150`)

```
execSystemRound(state, runBody, components, vars):
    1. (state_run, trace_run) = execStmts(state, runBody)
    2. (state_comp, trace_comp) = execComponents(state_run, components)
    3. state_snap = snapshot(state_comp, vars)
    4. state_next = nextRound(state_snap)
    return (state_next, trace_run ++ trace_comp ++ [Round(state.round)])
```

### 7.3 Component Execution (`Execution.lean:129`)

Execute each component's current state function in declaration order:

```
execComponents(state, [comp1, comp2, …]):
    for each comp in order:
        currentState = state.compState[comp.name]
        body = comp.states[currentState]
        if body exists:
            (state, trace_i) = execStmts(state, body)
    return (state, concat(traces))
```

### 7.4 Snapshot and Round Advance (`State.lean:82-88`)

After each round, snapshot current values into history:

```
snapshot(state, vars):
    for each x in vars:
        state.history[x][state.round] = state.env[x]

nextRound(state):
    state.round = state.round + 1
```

History is used by `[now-k]` expressions:
```
readHistory(state, x, k):
    targetRound = state.round + k     -- k is typically negative
    if targetRound >= 0:
        return state.history[x][targetRound]
    else:
        return Nil
```

---

## 8. Program Execution

Formal definition: `ExecProgram` (`Execution.lean:173`)

### 8.1 Spec Execution

```
execProgram(state, initBlock, runBlock, N, vars):
    1. (state_init, trace_init) = execStmts(state, initBlock)   -- once
    2. (state_final, trace_rounds) = execRounds(state_init, N, runBlock, vars)
    return (state_final, trace_init ++ trace_rounds)
```

The init block runs ONCE before round 0. The run block runs N times.

### 8.2 System Execution (`Execution.lean:199`)

```
execSystemProgram(state, initBlock, runBlock, components, N, vars):
    1. (state_init, trace_init) = execStmts(state, initBlock)
    2. (state_final, trace_rounds) = execSystemRounds(state_init, N, runBlock, components, vars)
    return (state_final, trace_init ++ trace_rounds)
```

### 8.3 Complete Pipeline

```
run(source):
    ast = parse(source)                           -- Section 2
    resolved = resolve(ast)                       -- Section 3
    state0 = buildInitialState(resolved)          -- Section 4
    (stateN, trace) = execProgram(                -- Section 8.1
        state0,
        resolved.initBlock,
        resolved.runBlock,
        resolved.rounds,
        resolved.varNames
    )
    checkAssertions(resolved.invariants, trace)   -- Section 9
```

---

## 9. Assertions and Model Checking

Formal definitions: `Temporal.lean`

### 9.1 Temporal Operators over Bounded Traces

Given a trace of states `[σ₀, σ₁, …, σₙ]` and predicate `P`:

| Operator            | Definition                                     |
|---------------------|-------------------------------------------------|
| `always P`          | `∀ i ∈ [0,N], P(σᵢ)`                          |
| `eventually P`      | `∃ i ∈ [0,N], P(σᵢ)`                          |
| `eventuallyAlways P`| `∃ k, ∀ i ≥ k, P(σᵢ)`                        |
| `nmt(n) P`          | at most `n` states satisfy P                   |
| `nft(n) P`          | at least `n` states satisfy P                  |

### 9.2 Assertion Checking (`Temporal.lean:65-77`)

An expression predicate is true when `eval(state, expr) == Bool(true)`.

- **`assert expr temporal`**: The assertion **holds** if the temporal property
  is satisfied. The model checker **negates** this — it searches for a trace
  where the assertion is violated.
- **`assume expr temporal`**: Constrains the search space. Only traces where
  the assumption holds are considered. NOT negated.

### 9.3 Conditional Assertions (`Temporal.lean:94-105`)

`assert when guard then body temporal` means:
```
at every state (per temporal modality):
    if eval(state, guard) == Bool(true):
        eval(state, body) must == Bool(true)
```

### 9.4 The Model Checking Problem (`Temporal.lean:124-135`)

A **counterexample** is a trace where:
1. ALL assumptions hold, AND
2. at least one assertion is violated

A model is **correct** when no counterexample exists.

For implementation, generate SMT constraints encoding all possible traces,
negate the assertions, and ask the solver for satisfiability.

---

## 10. SMT Encoding

The reference compiler generates SMT-LIB2 in `QF_NRA` (quantifier-free
nonlinear real arithmetic). The encoding strategy:

### 10.1 Variable Versioning

Each variable gets a version suffix per round (SSA style):
```
variable_0    -- initial value
variable_1    -- after round 1 assignment
variable_2    -- after conditional (phi node)
...
```

### 10.2 Assertions become constraints

| Fault                | SMT                                           |
|----------------------|-----------------------------------------------|
| `x = 30`            | `(assert (= x_0 30.0))`                      |
| `x <- y`            | `(assert (= x_1 (+ x_0 y_0)))`              |
| `x -> y`            | `(assert (= x_1 (- x_0 y_0)))`              |
| `if c { s }`        | `(assert (ite c s_true s_false))`             |
| `assert P`          | `(assert (not P))` (negated for counterexample search) |
| `assume P`          | `(assert P)` (not negated)                    |
| `f1 \| f2`          | generate all permutations, solver picks one   |
| `unknown()`         | free variable (unconstrained `declare-fun`)   |

### 10.3 Temporal Encoding

| Temporal           | SMT over rounds 0..N                                        |
|--------------------|--------------------------------------------------------------|
| `always P`         | `(and P_0 P_1 ... P_N)`                                    |
| `eventually P`     | `(or P_0 P_1 ... P_N)`                                     |
| `eventually-always`| `(or P_N (and P_{N-1} P_N) ... (and P_0 ... P_N))`        |
| `nft(n) P`         | `(or` all C(N+1,n) subsets where each element satisfies P `)` |
| `nmt(n) P`         | combinatorial: at most n can be true                         |

---

## 11. Nondeterminism and Unknowns

Formal definition: `EvalR` (`LTS.lean:74`)

### 11.1 The Two Evaluation Modes

- **Deterministic** (`eval`): for concrete execution and testing. Returns
  `Nil` for unknowns.
- **Relational** (`EvalR`): for reasoning about all possible behaviors.
  `Unknown` can take ANY value. `Uncertain(μ,σ)` can take any real.

### 11.2 Unknown Variables

When the model contains `unknown()`:
- The SMT encoding declares a free variable (no constraints on its value)
- The solver picks whatever value produces a counterexample
- In the LTS, `EvalR σ (Lit Unknown) v` holds for ALL `v`
- This means both branches of conditionals on unknowns are reachable

### 11.3 Uncertain Variables

`uncertain(μ, σ)` behaves like `unknown()` during solving — any real value
is allowed. The difference is that after solving, the result is annotated
with the probability of the chosen value under `N(μ, σ)`.

### 11.4 Choose / Parallel Nondeterminism

- `Choose([e1, e2, ...])` evaluates to any value that any `eᵢ` can produce
- `Parallel([s1, s2, ...])` executes the statements in any permutation order

For model checking, ALL nondeterministic choices must be explored.

---

## 12. Testing Against the Reference

To validate your implementation, compare against the Go reference compiler:

### 12.1 Build the Reference

```sh
cd /path/to/Fault && go build -o fault_bin .
```

### 12.2 Compare SMT Output

```sh
./fault_bin -m smt -f yourfile.fspec
```

Your implementation's SMT encoding should be logically equivalent
(not necessarily syntactically identical) to the reference output.

### 12.3 Compare Counterexamples

```sh
SOLVERCMD=z3 SOLVERARG="-in" ./fault_bin -f yourfile.fspec
```

Given the same assertions, your implementation should find the same
counterexamples (or equivalent ones).

### 12.4 Key Test Cases

From `generator/testdata/`:

| File | Tests |
|------|-------|
| `simple.fspec` | Basic stock + flow + conditional |
| `bathtub.fspec` | Parallel flows (`\|` operator) |
| `booleans.fspec` | Boolean stock + conditional toggle |
| `asserts.fspec` | Assertions + assumptions + counterexample |
| `unknowns.fspec` | Unknown variable resolution |
| `strings.fspec` | String-as-boolean logic |
| `history1.fspec` | `[now-1]` temporal references |
| `statecharts/statechart.fsystem` | Components + state transitions |

---

## Appendix: File Map

| Lean File | What It Defines |
|-----------|----------------|
| `Syntax.lean` | AST types: Val, Expr, Stmt, Spec, System, Invariant |
| `State.lean` | Runtime state: FaultState, SVal, Env, Label |
| `LTS.lean` | Evaluation (eval, EvalR), flow ops, transition relation (faultStep) |
| `Execution.lean` | Statement/round/program execution (ExecStmt, ExecRound, ExecProgram) |
| `Temporal.lean` | Temporal operators, assertion semantics, model checking |
| `Resolve.lean` | Name resolution, aliases, imports, component validation |
| `Properties.lean` | Proved properties (round monotonicity, snapshot invariants) |
| `Structural.lean` | Frame conditions (commutativity, idempotency, determinism) |
