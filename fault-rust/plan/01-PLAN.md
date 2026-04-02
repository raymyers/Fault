# Fault Rust Implementation Plan

Reimplement the Fault bounded model-checking compiler in Rust.
Source of truth: **Lean 4 semantics** in `semantics/FaultSemantics/`.
Validation oracle: **Go reference compiler** (this repo root, `go build -o fault_bin .`).

---

## Principles

1. **Lean semantics are authoritative.** When the Go compiler disagrees with the Lean formalization, file a bug against whichever is wrong—don't silently pick one.
2. **Data-driven tests.** Every behavior is covered by flat test-data files (`*.fspec` / `*.fsystem` input → expected output). No hand-rolled assertions that duplicate logic under test.
3. **Oracle comparison.** The Go compiler is the practical oracle. For each milestone, generate expected outputs with the Go binary and commit them as test fixtures. The Rust test suite diffs against these fixtures.
4. **Simplicity over cleverness.** Prefer boring Rust. Avoid macros, trait gymnastics, or deep generic towers unless they measurably reduce code or bugs.
5. **One concern per crate/module.** Mirror the Lean file layout: syntax, state, resolve, eval/lts, execution, temporal, smt.

---

## Test Data Convention

```
fault-rust/testdata/
  <name>/
    input.fspec          # or input.fsystem
    expected.smt2        # from: fault_bin -m smt -f input.fspec
    expected.result.json  # (optional) parsed counterexample
    oracle.sh            # script that regenerates expected.* from Go compiler
```

Tests read input, run the Rust pipeline, diff against `expected.*`.
Oracle scripts are idempotent and checked in.

Additional Lean-derived test vectors live in `fault-rust/testdata/lean/` and are produced from `semantics/test/`.

---

## Milestone 0 — Project Skeleton

- [x] `cargo init --lib fault-rust` with workspace layout
- [x] Crate structure: `fault_syntax`, `fault_resolve`, `fault_eval`, `fault_exec`, `fault_temporal`, `fault_smt`, `fault_cli`
- [x] CI: `cargo test`, `cargo clippy`, `cargo fmt --check`
- [x] Build Go oracle binary in CI (or document manual step)
- [x] Copy initial test fixtures from `generator/testdata/` into `fault-rust/testdata/`
- [x] Scaffold `oracle.sh` that runs Go compiler and writes `expected.*`

---

## Milestone 1 — AST / Syntax (`Syntax.lean`)

- [x] Define `Val` enum (`Nat`, `Float`, `Bool`, `Str`, `Unknown`, `Uncertain(f64,f64)`, `Nil`)
- [x] Define `BinOp`, `UnOp`, `FlowOp` enums
- [x] Define `Expr` enum (`Lit`, `Var`, `BinOp`, `UnOp`, `Dot`, `History`, `Choose`)
- [x] Define `Stmt` enum (`FlowAssign`, `IfThenElse`, `Call`, `Advance`, `Stay`, `Seq`, `Parallel`)
- [x] Define `Temporal` enum (`Always`, `Eventually`, `EventuallyAlways`, `Nmt(u64)`, `Nft(u64)`)
- [x] Define `Invariant` enum (`Assert`, `Assume`, `AssertWhen`, `AssumeWhen`)
- [x] Define `StockDef`, `FlowDef`, `CompDef`, `Spec`, `System` structs
- [x] Serde JSON round-trip tests against a hand-written AST snapshot

---

## Milestone 2 — Parser (ANTLR grammar → Rust)

Strategy: use `pest`, `lalrpop`, or a hand-written recursive-descent parser targeting the ANTLR grammar in `grammar/FaultParser.g4`.

- [x] Lex `.fspec` files into token stream
- [x] Parse spec-level constructs: `spec`, `def`, `stock`, `flow`, `for N init{} run{}`
- [x] Parse expressions: arithmetic, comparison, logical, `||` (choose), `[now±k]`
- [x] Parse statements: `=`, `<-`, `->`, `if/else`, function call, `|` (parallel)
- [x] Parse invariants: `assert`, `assume`, `assert when...then`, temporal modalities
- [x] Parse `.fsystem` files: `import`, `component`, `start`
- [x] **Data test:** for each fixture in `testdata/`, parse to AST without errors (all fixtures parse)

---

## Milestone 3 — Name Resolution (`Resolve.lean`)

- [x] `flatten_name(parts: &[&str]) -> String` — join with `_`
- [x] Scope context: prepend `[spec_name] ++ scope_parts` to identifiers
- [x] Alias resolution (stock swaps): recursive lookup with cycle limit (`Resolve.lean:49`)
- [x] `resolve_expr`: eliminate `Expr::Dot` → `Expr::Var(flat_name)` (`Resolve.lean:68`)
- [x] `resolve_stmt`, `resolve_invariant`: walk full AST
- [x] Import resolution for `.fsystem`: merge stocks/flows/constants, keep invariants, ignore imported run blocks (`Resolve.lean:108`)
- [x] Component validation: state functions must not contain `FlowAssign` (`Resolve.lean:134`)
- [x] Build `ResolvedProgram` struct (`Resolve.lean:158`)
- [x] **Data test:** resolve fixtures, verify no Dot nodes remain after resolution

---

## Milestone 4 — State & Evaluation (`State.lean`, `LTS.lean`)

- [x] Define `SVal` enum (`Real(f64)`, `Bool(bool)`, `Nil`)
- [x] Define `FaultState` struct (`env: HashMap<Name, SVal>`, `round: u64`, `comp_state: HashMap<Name, Name>`, `history: HashMap<(Name, u64), SVal>`)
- [x] `to_sval(val: &Val) -> SVal` conversion (numerics→Real, Str→Bool(false), Unknown/Uncertain→Nil for concrete eval)
- [x] `build_initial_state(program: &ResolvedProgram) -> FaultState` (`State.lean:98`)
- [x] `eval(state: &FaultState, expr: &Expr) -> SVal` — deterministic evaluator (`LTS.lean:23`)
- [x] Arithmetic: `add`, `sub`, `mul`, `div`, `mod`, `exp` on reals
- [x] Comparison: `eq`, `neq`, `lt`, `le`, `gt`, `ge` → `SVal::Bool`
- [x] Logical: `and`, `or`, `not` on bools
- [x] `History(name, offset)` → lookup `state.history[(name, round+offset)]`
- [x] `Choose(exprs)` → Nil (deterministic mode; nondeterminism at SMT level)
- [x] `Nil` propagation: any op with `Nil` → `Nil`
- [x] Flow operators: `apply_flow(op, current, value) -> SVal` (`LTS.lean:42`)
- [x] **Data test:** 20 unit tests covering all operations, state, history, flow ops

---

## Milestone 5 — Statement Execution (`Execution.lean`)

- [x] `exec_stmt(state: &mut FaultState, stmt: &Stmt, flows: &FlowMap) -> Vec<Label>`
- [x] `FlowAssign`: `state.env[name] = apply_flow(op, state.env[name], eval(expr))`
- [x] `IfThenElse`: eval condition, execute appropriate branch
- [x] `Call(func_name)`: lookup function body in flows, execute it
- [x] `Advance(target)`: emit label (comp state handled at system level)
- [x] `Stay`: no-op
- [x] `Seq(stmts)`: execute in order
- [x] `Parallel(stmts)`: canonical order (sequential in declaration order)
- [x] `exec_stmts(state, stmts)` — sequential block execution (`Execution.lean:80`)
- [x] **Data test:** unit tests for simple spec, bathtub parallel, flow ops, if/else, call, rounds

---

## Milestone 6 — Round & Program Execution (`Execution.lean:120+`)

- [x] `exec_round`: run block → snapshot history → increment round
- [x] `snapshot_history(state)`: `∀ name, history[(name, round)] = env[name]`
- [x] `exec_rounds(state, n, run_block, vars) -> (FaultState, Trace)`
- [x] `exec_system_round`: run block + per-component state function dispatch
- [x] `exec_program(state, init_block, run_block, n)` — init once, then N rounds (`Execution.lean:173`)
- [x] `exec_system_program(state, init, run, components, n)` (`Execution.lean:199`)
- [x] **Data test:** round snapshot/advance, multi-round accumulation, bathtub parallel rounds

---

## Milestone 7 — Temporal Logic & Assertions (`Temporal.lean`)

- [x] `check_always(trace, pred) -> bool`
- [x] `check_eventually(trace, pred) -> bool`
- [x] `check_eventually_always(trace, pred) -> bool`
- [x] `check_nmt(n, trace, pred) -> bool`
- [x] `check_nft(n, trace, pred) -> bool`
- [x] `check_invariant(trace, invariant) -> CheckResult`
- [x] Assertion negation: `assert P` → search for `¬P` (at SMT level)
- [x] Assumption filtering: `assume P` → constrain, no negation
- [x] Conditional assertions: `assert when guard then body temp`
- [x] **Data test:** 15 unit tests covering all temporal operators, invariant checking, edge cases

---

## Milestone 8 — SMT Encoding

- [x] Variable versioning (SSA-style): `name_0`, `name_1`, ... per round
- [x] Emit `(set-logic QF_NRA)`
- [x] Emit `(declare-fun ...)` for each versioned variable
- [x] Encode `FlowAssign` → `(assert (= ...))` with `Assign`/`Inflow`/`Outflow` semantics
- [x] Encode `IfThenElse` → `(assert (ite ...))` with branch tracking booleans
- [x] Encode `Parallel` → canonical order (permutation disjuncts TODO)
- [x] Encode temporal assertions → conjunction/disjunction over rounds (§10.3)
- [x] Negate assertions, keep assumptions
- [x] `unknown()` → `(declare-fun x () Real)` with no constraints
- [x] `uncertain(μ,σ)` → same as unknown for solving
- [x] **Data test:** 7 unit tests: SSA versioning, literal encoding, temporal combinatorics, simple/unknown program encoding

---

## Milestone 9 — Solver Integration & End-to-End

- [x] Shell out to Z3 with generated SMT-LIB2 (SOLVERCMD/SOLVERARG env vars)
- [x] Parse solver response: `sat` / `unsat` / `unknown`
- [x] Extract model values on `sat`
- [x] CLI: `fault-rust -f input.fspec` → counterexample or "correct"
- [x] CLI: `fault-rust -m smt -f input.fspec` → print SMT encoding
- [x] CLI: `fault-rust -m parse -f input.fspec` → dump AST (debug)
- [x] Fixed: spec name from parsed `spec` declaration, not filename
- [x] Fixed: invariant name resolution via name_map (stock→qualified)
- [x] Fixed: if-then-else SSA versioning (correct phi nodes)
- [x] **End-to-end data test:** 3 e2e tests (simpleA, asserts, unknowns) — structurally matching Go oracle output

---

## Milestone 10 — Edge Cases & Completeness

- [x] Flow-level scalar properties (`value: 0` on flows → `__val_*` synthetic stocks)
- [x] `this` keyword in flow functions → resolves to instance prefix
- [x] Boolean-sorted variables (`Bool` instead of `Real` when stock value is bool)
- [x] Else-branch encoding (both branches generate SMT; ITE selects phi)
- [x] History references across rounds — `history1-4.fspec` (round_entries snapshots)
- [x] **Data test:** 3 new e2e tests (booleans, increment, history1) — 114 total tests pass
- [x] String-as-boolean (`Str → Bool(false)`) — `strings.fspec`
- [x] Stock swaps — `swaps/` directory
- [x] Multi-file imports — `imports/` directory
- [x] Bad spec error reporting — `badspecs/` directory
- [x] Indexes — `indexes.fspec`
- [x] `bathtub2.fspec` (multiple parallel flows)
- [ ] Full statechart system — `statecharts/`
- [ ] **Data test:** each of the above has oracle fixture; all pass

---

## Dependency Graph

```
M0 (skeleton)
 └─→ M1 (AST) ─→ M2 (parser) ─→ M3 (resolve)
                                      │
                                      ├─→ M4 (state/eval)
                                      │      │
                                      │      └─→ M5 (stmt exec) ─→ M6 (rounds/program)
                                      │                                    │
                                      │                              M7 (temporal)
                                      │                                    │
                                      └────────────────────────→ M8 (SMT) ─→ M9 (solver/E2E)
                                                                                  │
                                                                            M10 (completeness)
```

---

## Lean File → Rust Module Map

| Lean File          | Rust Module           | Purpose                                    |
|--------------------|-----------------------|--------------------------------------------|
| `Syntax.lean`      | `fault_syntax`        | AST types: Val, Expr, Stmt, Spec, System   |
| `Resolve.lean`     | `fault_resolve`       | Name flattening, alias resolution, imports |
| `State.lean`       | `fault_eval::state`   | FaultState, SVal, initial state builder    |
| `LTS.lean`         | `fault_eval::eval`    | Expression evaluation, flow operators      |
| `Execution.lean`   | `fault_exec`          | Statement/round/program execution          |
| `Temporal.lean`    | `fault_temporal`      | Temporal operators, assertion checking     |
| —                  | `fault_smt`           | SMT-LIB2 code generation                  |
| —                  | `fault_cli`           | CLI binary                                 |
