# Fault Language: Operational Semantics in Lean 4 with CSLib LTS

## Goal

Formalize the operational semantics of the Fault modeling language as a Labeled Transition System (LTS) in Lean 4 using the [CSLib LTS framework](https://api.cslib.io/docs/Cslib/Foundations/Semantics/LTS/Basic.html), and verify behavioral equivalence against the Go compiler implementation.

---

## Phase 0: Project Setup

- [x] Initialize a Lean 4 Lake project under `semantics/` (or a sibling repo)
- [x] Add CSLib as a dependency (`require cslib from git ...`)
- [x] Confirm `import Cslib.Foundations.Semantics.LTS.Basic` builds
- [ ] Set up a test harness that can shell out to the Go compiler for oracle comparison

---

## Phase 1: Abstract Syntax

Encode the Fault AST as Lean inductive types. Source of truth: `ast/ast.go`.

- [x] Define `Val`, `BinOp`, `UnOp`, `FlowOp` inductive types
- [x] Define `Expr` inductive type (lit, var, binop, unop, history, choose)
- [x] Define `Stmt` inductive type (flowAssign, ifThenElse, call, advance, stay, seq)
- [x] Define `StockDef`, `FlowDef`, `CompDef`, `Spec`, `System` structures
- [ ] Round-trip test: parse `.fspec`/`.fsystem` with Go compiler (`-m ast`), export JSON, compare against Lean AST

### 1.1 Core Types

```
inductive Val        -- Nat, Float (ℝ), Bool, Unknown, Uncertain μ σ
inductive BinOp      -- Add, Sub, Mul, Div, Mod, Exp, Eq, Neq, Lt, Le, Gt, Ge, And, Or
inductive UnOp       -- Neg, Not
inductive FlowOp     -- Assign (=), Inflow (←), Outflow (→)
```

### 1.2 Expressions

```
inductive Expr
  | lit      : Val → Expr
  | var      : Name → Expr
  | binop    : BinOp → Expr → Expr → Expr
  | unop     : UnOp → Expr → Expr
  | history  : Name → ℤ → Expr          -- x[now - k]
  | choose   : List Expr → Expr          -- nondeterministic choice (||)
```

### 1.3 Statements & Declarations

```
inductive Stmt
  | flowAssign : Name → FlowOp → Expr → Stmt    -- stock ← e, stock → e, stock = e
  | ifThenElse : Expr → List Stmt → List Stmt → Stmt
  | call       : Name → Stmt                     -- invoke a flow function
  | advance    : Name → Stmt                     -- state transition
  | stay       : Stmt
  | seq        : List Stmt → Stmt

structure StockDef   := (name : Name) (props : List (Name × Val))
structure FlowDef    := (name : Name) (stocks : List (Name × Name)) (funcs : List (Name × List Stmt))
structure CompDef    := (name : Name) (states : List (Name × List Stmt))
structure Spec       := (stocks : List StockDef) (flows : List FlowDef) (constants : List (Name × Val))
structure System     := (imports : List Spec) (components : List CompDef) (startStates : List (Name × Name))
```

---

## Phase 2: Semantic Domains (State and Labels)

### 2.1 State

- [x] Define `FaultState` structure (env, round, compState, history)
- [x] Define `Label` inductive type (tau, flowExec, stateEntry, assign, branch, round)
- [x] Instantiate `Cslib.LTS FaultState Label` with `Tr := faultStep`
- [x] Prove key invariant: `history x round = env x` at end of each round

The global state of a Fault model at a given point in execution:

```
structure FaultState where
  env       : Name → Val                      -- stock property values (the "store")
  round     : ℕ                               -- current simulation round
  compState : Name → Name                     -- component → current state name
  history   : Name → ℕ → Val                  -- variable → round → value (for [now-k])
```

Key invariant: `history x round = env x` at the end of each round.

### 2.2 Labels

Labels represent observable actions in the LTS:

```
inductive Label
  | tau                                        -- internal/silent step
  | flowExec   : Name → Name → Label          -- flow.func executed
  | stateEntry : Name → Name → Label          -- component enters state
  | assign     : Name → FlowOp → Val → Label  -- stock modified
  | branch     : Bool → Label                  -- conditional branch taken (true/false)
  | round      : ℕ → Label                    -- round boundary marker
```

### 2.3 LTS Instantiation

Using the CSLib structure:

```lean
def FaultLTS : Cslib.LTS FaultState Label where
  Tr := faultStep  -- defined in Phase 3
```

---

## Phase 3: Small-Step Operational Semantics

Define `faultStep : FaultState → Label → FaultState → Prop` as the transition relation.

- [x] Define `eval` (big-step expression evaluation, set-valued)
- [x] Define transition rules: Assign, Inflow, Outflow
- [x] Define transition rules: IfTrue, IfFalse (conditional branching)
- [x] Define transition rules: Call (flow function invocation)
- [x] Define transition rules: Advance, Stay (component state transitions)
- [x] Define transition rule: Seq (sequential composition)
- [x] Define `roundStep` (run block → component steps → snapshot → increment)
- [x] Define parallel composition for `|` operator (all permutations)
- [x] Define system-level composition (multiple components per round)

### 3.1 Expression Evaluation (Big-Step, Pure)

```
def eval (σ : FaultState) : Expr → Set Val
```

- Deterministic for concrete values
- Set-valued for `unknown()` (any value) and `uncertain(μ,σ)` (any real, probability weight tracked separately)
- `choose [e₁, ..., eₙ]` returns `⋃ᵢ eval σ eᵢ`
- `history x k` returns `σ.history x (σ.round - k)`

### 3.2 Statement Transitions

One rule per statement form:

| Rule | Premise | Label | Effect on State |
|------|---------|-------|-----------------|
| **Assign** | `v ∈ eval σ e` | `assign x Assign v` | `σ.env[x] := v` |
| **Inflow** | `v ∈ eval σ e` | `assign x Inflow v` | `σ.env[x] := σ.env[x] + v` |
| **Outflow** | `v ∈ eval σ e` | `assign x Outflow v` | `σ.env[x] := σ.env[x] - v` |
| **IfTrue** | `eval σ cond ∋ true` | `branch true` | continue with then-branch |
| **IfFalse** | `eval σ cond ∋ false` | `branch false` | continue with else-branch |
| **Call** | look up function body | `flowExec flow func` | execute function body statements |
| **Advance** | component `c` in state `s` | `stateEntry c s'` | `σ.compState[c] := s'` |
| **Stay** | — | `tau` | no state change |
| **Seq** | — | — | chain: `s₁ →* s₂ →* ... →* sₙ` |

### 3.3 Round Semantics

A single round of `for N init{...} run{...}`:

1. Execute each statement in the `run` block sequentially
2. For each active component, execute its current state function
3. Snapshot: `∀ x, history x round := env x`
4. Increment round counter
5. Emit `round n` label

This matches the Go compiler's behavior in `runner/runner.go` and `llvm/compiler.go` where:
- The run block is compiled as a function executed per round
- Component state functions fire after the run block
- SSA versioning creates per-round snapshots (aligning with our history model)

### 3.4 Parallel Composition (`|` operator)

When `f₁ | f₂` appears, model as nondeterministic interleaving:

```
∀ perm ∈ permutations [f₁, f₂],
  σ →[exec perm[0]] σ₁ →[exec perm[1]] σ₂
```

This matches `generator/rules/rules.go` `Parallels` rule type, which generates all permutations.

### 3.5 System-Level Composition

Multiple components execute within a round. The full round transition is:

```
roundStep σ σ' ≡ ∃ σ_mid,
  (runBlockSteps σ σ_mid) ∧
  (componentSteps σ_mid σ') ∧
  σ'.round = σ.round + 1
```

---

## Phase 4: Assertion and Temporal Semantics

- [x] Define `Trace` type using CSLib's `MTr` (multistep transition)
- [x] Formalize `always`, `eventually`, `eventually-always`, `nft`, `nmt` over bounded traces
- [x] Formalize assertion negation (`assert φ` ↦ solver checks `¬φ`)
- [x] Formalize `assume` as trace-space constraint (no negation)
- [ ] Prove equivalence between formal temporal definitions and SMT encodings from `asserts.go`

### 4.1 Traces

A trace is a finite execution of the LTS (using CSLib's `Execution` or `MTr`):

```
def Trace := lts.MTr σ₀ μs σₙ   -- multistep transition from initial to final state
```

### 4.2 Temporal Operators over Bounded Traces

Given a trace of length N and a predicate P on states:

| Operator | Formal Definition | SMT Encoding (from `asserts.go`) |
|----------|-------------------|----------------------------------|
| `always P` | `∀ i ∈ [0,N], P(σᵢ)` | `(and P₀ P₁ ... Pₙ)` |
| `eventually P` | `∃ i ∈ [0,N], P(σᵢ)` | `(or P₀ P₁ ... Pₙ)` |
| `eventually-always P` | `∃ k ∈ [0,N], ∀ i ∈ [k,N], P(σᵢ)` | `(or (Pₙ) (P_{n-1} ∧ Pₙ) ... (P₀ ∧ ... ∧ Pₙ))` |
| `nft n P` | `|{i : P(σᵢ)}| ≥ n` | `(or ⋁_{S ∈ C(N,n)} ⋀_{i∈S} Pᵢ)` |
| `nmt n P` | `|{i : P(σᵢ)}| ≤ n` | combinatorial constraint (see `asserts.go:484`) |

### 4.3 Assertion Negation

The core semantic of `assert φ` in Fault: the compiler generates `¬φ` and asks the solver if it's satisfiable. A SAT result means a counterexample exists (the assertion can be violated).

```
def assertionHolds (lts : FaultLTS) (σ₀ : FaultState) (φ : Assertion) : Prop :=
  ∀ (σₙ : FaultState) (μs : List Label),
    lts.MTr σ₀ μs σₙ → φ.predicate σₙ
```

An assertion **fails** when `∃ trace, ¬(φ.predicate σₙ)` — which is exactly what the SMT solver searches for.

### 4.4 Assumptions

`assume ψ` constrains the state space without negation:

```
def withAssumption (ψ : FaultState → Prop) (traces : Set Trace) : Set Trace :=
  { t ∈ traces | ∀ σᵢ ∈ t.states, ψ σᵢ }
```

---

## Phase 5: CSLib LTS Properties

Leverage CSLib's built-in theory to prove structural properties of FaultLTS.

- [x] Prove basic properties (stay always available, assignment/advance locality)
- [x] Prove round counter monotonicity
- [x] Prove temporal implications (always→eventually, eventuallyAlways→eventually)
- [ ] Prove `noNondet spec → Deterministic (faultLTSOf spec)`
- [ ] Prove `FinitelyBranching FaultLTS`
- [ ] Prove `FiniteLTS (boundedFaultLTS N)` for bounded models
- [ ] (Stretch) Prove bisimulation-based spec equivalence using CSLib `Bisimilarity`

### 5.1 Determinism Analysis

- **FaultLTS is NOT deterministic** in general (due to `unknown()`, `uncertain()`, `choose`, and `|`)
- However, a Fault model with no unknowns/uncertains and no `|` operators IS deterministic
- Prove: `noNondet spec → Deterministic (faultLTSOf spec)`

### 5.2 Finite Branching

- Each round has finitely many possible transitions (finite permutations, finite branches)
- Prove: `FinitelyBranching FaultLTS`
- This guarantees decidability of reachability (bounded)

### 5.3 Acyclicity / Finite LTS

- With bounded `for N`, the state space is finite (N rounds × finite branching)
- Prove: `FiniteLTS (boundedFaultLTS N)`

### 5.4 Bisimulation (Optional/Future)

- Two Fault specs are behaviorally equivalent iff their LTSs are bisimilar
- CSLib provides `Bisimilarity` and proof infrastructure
- Could be used for spec refactoring validation

---

## Phase 6: Verification Against Go Implementation

- [x] Build test harness: shell out to Go compiler, capture `-m ir` and `-m smt` output
- [ ] Write Lean parsers for LLVM IR and SMT-LIB2 output
- [x] Trace comparison: run Lean semantics on test inputs, compare reachable states with Go
- [x] Counterexample validation: verify Go SAT results produce matching Lean LTS traces
- [x] SMT equivalence: compare Go-generated SMT with Lean-derived constraints (small models)
- [x] Verify each specific equivalence in the table below (10 properties)
- [ ] (Stretch) Mechanized bisimulation: `GoStyleLTS` ∼ `FaultLTS`

### 6.1 Strategy: Oracle Testing

The Go compiler is the reference implementation. We verify the Lean semantics by:

1. **Trace comparison**: For each test case, run the Go compiler with `-m ir` and `-m smt` to extract the LLVM IR and SMT encoding. Execute the Lean semantics on the same input. Compare reachable states.

2. **Counterexample validation**: When the Go compiler reports a counterexample (SAT result with variable assignments), verify that the Lean LTS can produce a matching trace.

3. **SMT equivalence**: For small models, compare the SMT formula generated by Go with the constraints derivable from the Lean LTS semantics.

### 6.2 Test Infrastructure

```
semantics/
  test/
    oracle/
      run_go_compiler.sh      -- invoke Fault Go compiler, capture output
      parse_ir.lean            -- parse LLVM IR output into Lean structures
      parse_smt.lean           -- parse SMT-LIB2 output for comparison
    cases/
      battery.fspec            -- from examples repo
      fibonacci.fspec
      sandwich.fspec
      cache.fspec
      drone.fsystem
      repl.fsystem
```

### 6.3 Specific Equivalences to Verify

| Property | Go Implementation (source) | Lean Formalization |
|----------|---------------------------|-------------------|
| Stock inflow `←` | `llvm/compiler.go:927` — store to alloc | `faultStep` Inflow rule: `env[x] + v` |
| Stock outflow `→` | `llvm/compiler.go` — sub + store | `faultStep` Outflow rule: `env[x] - v` |
| Conditional phi | `unroll/unroll.go:474` — OnEntry/PhiLevel | `faultStep` IfTrue/IfFalse with continuation |
| Temporal `eventually` | `asserts/asserts.go:393` — `(or s₀ ... sₙ)` | `∃ i, P(σᵢ)` over bounded trace |
| Temporal `eventually-always` | `asserts/asserts.go:544` — progressive conjunction | `∃ k, ∀ i≥k, P(σᵢ)` |
| Parallel `\|` | `rules/rules.go` Parallels — all permutations | nondeterministic interleaving in LTS |
| SSA versioning per round | `alloc.go:13` — `updateVariableStateName` | `history x round` snapshot |
| Assertion negation | `asserts/asserts.go:266` — `applyWhen` flip | `¬φ` satisfiability = counterexample search |
| Unknown values | `execute/execute.go:22` — free SMT variable | `eval` returns full `Set Val` |
| Component transitions | `compiler.go` advance/stay compilation | `stateEntry` / `tau` labels |

### 6.4 Mechanized Bisimulation (Stretch Goal)

Define a "reference LTS" that directly mirrors the Go compiler's SSA-based state representation (versioned variable names, explicit phi contexts). Prove this is bisimilar to the cleaner mathematical LTS from Phase 3. This would give a machine-checked proof that the Lean semantics faithfully captures the Go compiler's behavior.

```lean
def GoStyleState := Name → ℕ → Val   -- variable name → SSA version → value
def GoStyleLTS : Cslib.LTS GoStyleState Label := ...

theorem go_lean_bisimilar :
  Bisimilarity FaultLTS.toLTS GoStyleLTS.toLTS := by ...
```

---

## Phase 7: Milestones and Dependencies

```
Phase 0 ──→ Phase 1 ──→ Phase 2 ──→ Phase 3 ──→ Phase 4
  (setup)     (AST)      (domains)   (steps)     (temporal)
                                        │
                                        ↓
                                    Phase 5      Phase 6
                                   (properties)  (verification)
                                        │            │
                                        └────────────┘
                                              ↓
                                    Phase 6.4 (bisimulation)
```

### Milestone 1: Minimal .fspec semantics
- [x] Phases 0-3 for the subset: stocks, flows (`=`, `←`, `→`), conditionals, `for N` loops
- [x] Oracle test on `fibonacci.fspec` and `sandwich.fspec`

### Milestone 2: Assertions and temporal logic
- [x] Phase 4 complete
- [x] Oracle test: assert counterexamples match Go compiler on `battery.fspec`

### Milestone 3: Components and .fsystem
- [ ] Phase 3 extended with component/state transitions
- [ ] Oracle test on `drone.fsystem` and `repl.fsystem`

### Milestone 4: Full nondeterminism
- [ ] `unknown()`, `uncertain()`, `|` operator
- [ ] Phase 5 properties proved
- [ ] Phase 6 verification complete

---

## Open Questions

- [ ] Resolve each question below before or during the relevant phase

1. **Uncertain value semantics**: The Go compiler treats `uncertain(μ,σ)` as a free variable during solving, with probability annotated post-hoc. Should the Lean semantics model this as a probability measure over traces, or keep the simpler "free variable + annotation" model?

2. **Component scheduling order**: When multiple components are active in a round, is execution order fixed (declaration order) or nondeterministic? The Go compiler appears to use declaration order via `SpecRecord.Order`. Need to confirm.

3. **Swaps**: `cluster.p = pool2` mid-execution (flow stock swapping) — what are the exact semantics? See `Bellmar/swaps` commit 664e160.

4. **`when ... then` assertions**: The Go compiler's `applyWhen` (asserts.go:258) generates implication rules. Need to formalize the scoping — does `when` apply per-round or across the whole trace?

5. **LLVM optimization passes**: Recent commit `1f8d04c` added optimization passes. Do these change observable semantics, or are they purely performance? Need to verify semantic preservation.
