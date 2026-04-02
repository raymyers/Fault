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

- [ ] `cargo init --lib fault-rust` with workspace layout
- [ ] Crate structure: `fault_syntax`, `fault_resolve`, `fault_eval`, `fault_exec`, `fault_temporal`, `fault_smt`, `fault_cli`
- [ ] CI: `cargo test`, `cargo clippy`, `cargo fmt --check`
- [ ] Build Go oracle binary in CI (or document manual step)
- [ ] Copy initial test fixtures from `generator/testdata/` into `fault-rust/testdata/`
- [ ] Scaffold `oracle.sh` that runs Go compiler and writes `expected.*`

---

## Milestone 1 — AST / Syntax (`Syntax.lean`)

- [ ] Define `Val` enum (`Nat`, `Float`, `Bool`, `Str`, `Unknown`, `Uncertain(f64,f64)`, `Nil`)
- [ ] Define `BinOp`, `UnOp`, `FlowOp` enums
- [ ] Define `Expr` enum (`Lit`, `Var`, `BinOp`, `UnOp`, `Dot`, `History`, `Choose`)
- [ ] Define `Stmt` enum (`FlowAssign`, `IfThenElse`, `Call`, `Advance`, `Stay`, `Seq`, `Parallel`)
- [ ] Define `Temporal` enum (`Always`, `Eventually`, `EventuallyAlways`, `Nmt(u64)`, `Nft(u64)`)
- [ ] Define `Invariant` enum (`Assert`, `Assume`, `AssertWhen`, `AssumeWhen`)
- [ ] Define `StockDef`, `FlowDef`, `CompDef`, `Spec`, `System` structs
- [ ] Serde JSON round-trip tests against a hand-written AST snapshot

---

## Milestone 2 — Parser (ANTLR grammar → Rust)

Strategy: use `pest`, `lalrpop`, or a hand-written recursive-descent parser targeting the ANTLR grammar in `grammar/FaultParser.g4`.

- [ ] Lex `.fspec` files into token stream
- [ ] Parse spec-level constructs: `spec`, `def`, `stock`, `flow`, `for N init{} run{}`
- [ ] Parse expressions: arithmetic, comparison, logical, `||` (choose), `[now±k]`
- [ ] Parse statements: `=`, `<-`, `->`, `if/else`, function call, `|` (parallel)
- [ ] Parse invariants: `assert`, `assume`, `assert when...then`, temporal modalities
- [ ] Parse `.fsystem` files: `import`, `component`, `start`
- [ ] **Data test:** for each fixture in `testdata/`, parse to AST, serialize to JSON, compare to Go compiler AST output (`fault_bin -m ast`)

---

## Milestone 3 — Name Resolution (`Resolve.lean`)

- [ ] `flatten_name(parts: &[&str]) -> String` — join with `_`
- [ ] Scope context: prepend `[spec_name] ++ scope_parts` to identifiers
- [ ] Alias resolution (stock swaps): recursive lookup with cycle limit (`Resolve.lean:49`)
- [ ] `resolve_expr`: eliminate `Expr::Dot` → `Expr::Var(flat_name)` (`Resolve.lean:68`)
- [ ] `resolve_stmt`, `resolve_invariant`: walk full AST
- [ ] Import resolution for `.fsystem`: merge stocks/flows/constants, keep invariants, ignore imported run blocks (`Resolve.lean:108`)
- [ ] Component validation: state functions must not contain `FlowAssign` (`Resolve.lean:134`)
- [ ] Build `ResolvedProgram` struct (`Resolve.lean:158`)
- [ ] **Data test:** resolve fixtures, compare flattened names against Go compiler output

---

## Milestone 4 — State & Evaluation (`State.lean`, `LTS.lean`)

- [ ] Define `SVal` enum (`Real(f64)`, `Bool(bool)`, `Nil`)
- [ ] Define `FaultState` struct (`env: HashMap<Name, SVal>`, `round: u64`, `comp_state: HashMap<Name, Name>`, `history: HashMap<(Name, u64), SVal>`)
- [ ] `to_sval(val: &Val) -> SVal` conversion (numerics→Real, Str→Bool(false), Unknown/Uncertain→Nil for concrete eval)
- [ ] `build_initial_state(program: &ResolvedProgram) -> FaultState` (`State.lean:98`)
- [ ] `eval(state: &FaultState, expr: &Expr) -> SVal` — deterministic evaluator (`LTS.lean:23`)
- [ ] Arithmetic: `add`, `sub`, `mul`, `div`, `mod`, `exp` on reals
- [ ] Comparison: `eq`, `neq`, `lt`, `le`, `gt`, `ge` → `SVal::Bool`
- [ ] Logical: `and`, `or`, `not` on bools
- [ ] `History(name, offset)` → lookup `state.history[(name, round+offset)]`
- [ ] `Choose(exprs)` → pick first non-Nil (deterministic mode)
- [ ] `Nil` propagation: any op with `Nil` → `Nil`
- [ ] Flow operators: `apply_flow(op, current, value) -> SVal` (`LTS.lean:42`)
- [ ] **Data test:** for each fixture, build initial state, eval known expressions, compare against hand-checked values

---

## Milestone 5 — Statement Execution (`Execution.lean`)

- [ ] `exec_stmt(state: &mut FaultState, stmt: &Stmt, flows: &FlowMap) -> Vec<Label>`
- [ ] `FlowAssign`: `state.env[name] = apply_flow(op, state.env[name], eval(expr))`
- [ ] `IfThenElse`: eval condition, execute appropriate branch
- [ ] `Call(func_name)`: lookup function body in flows, execute it
- [ ] `Advance(target)`: `state.comp_state[comp] = target`
- [ ] `Stay`: no-op
- [ ] `Seq(stmts)`: execute in order
- [ ] `Parallel(stmts)`: execute all permutations (for oracle matching, use canonical order first)
- [ ] `exec_stmts(state, stmts)` — sequential block execution (`Execution.lean:80`)
- [ ] **Data test:** single-round execution on `simple.fspec`, `bathtub.fspec`, compare env state vs Go

---

## Milestone 6 — Round & Program Execution (`Execution.lean:120+`)

- [ ] `exec_round`: run block → component steps → snapshot history → increment round
- [ ] `snapshot_history(state)`: `∀ name, history[(name, round)] = env[name]`
- [ ] `exec_rounds(state, n, run_block, vars) -> (FaultState, Trace)`
- [ ] `exec_system_round`: run block + per-component state function dispatch
- [ ] `exec_program(state, init_block, run_block, n)` — init once, then N rounds (`Execution.lean:173`)
- [ ] `exec_system_program(state, init, run, components, n)` (`Execution.lean:199`)
- [ ] **Data test:** multi-round traces on `simple.fspec` (1 round), `history1.fspec` (temporal refs), `statecharts/statechart.fsystem` (components). Compare full trace against Go.

---

## Milestone 7 — Temporal Logic & Assertions (`Temporal.lean`)

- [ ] `check_always(trace, pred) -> bool`
- [ ] `check_eventually(trace, pred) -> bool`
- [ ] `check_eventually_always(trace, pred) -> bool`
- [ ] `check_nmt(n, trace, pred) -> bool`
- [ ] `check_nft(n, trace, pred) -> bool`
- [ ] `check_invariant(trace, invariant) -> CheckResult`
- [ ] Assertion negation: `assert P` → search for `¬P`
- [ ] Assumption filtering: `assume P` → constrain, no negation
- [ ] Conditional assertions: `assert when guard then body temp`
- [ ] **Data test:** `asserts.fspec` — assertion pass/fail matches Go compiler

---

## Milestone 8 — SMT Encoding

- [ ] Variable versioning (SSA-style): `name_0`, `name_1`, ... per round
- [ ] Emit `(set-logic QF_NRA)`
- [ ] Emit `(declare-fun ...)` for each versioned variable
- [ ] Encode `FlowAssign` → `(assert (= ...))` with `Assign`/`Inflow`/`Outflow` semantics
- [ ] Encode `IfThenElse` → `(assert (ite ...))`
- [ ] Encode `Parallel` → all permutations as disjuncts
- [ ] Encode temporal assertions → conjunction/disjunction over rounds (see `semantics/docs/implementation.md` §10.3)
- [ ] Negate assertions, keep assumptions
- [ ] `unknown()` → `(declare-fun x () Real)` with no constraints
- [ ] `uncertain(μ,σ)` → same as unknown for solving, annotate result
- [ ] **Data test:** for every `.fspec` in `testdata/`, generate `.smt2`, diff against `expected.smt2` from Go compiler. Allow reordering of independent asserts.

---

## Milestone 9 — Solver Integration & End-to-End

- [ ] Shell out to Z3 (or use z3-sys crate) with generated SMT-LIB2
- [ ] Parse solver response: `sat` (counterexample found) / `unsat` (correct) / `unknown`
- [ ] Extract model values on `sat`
- [ ] CLI: `fault-rust -f input.fspec` → counterexample or "correct"
- [ ] CLI: `fault-rust -m smt -f input.fspec` → print SMT encoding
- [ ] **End-to-end data test:** for all fixtures, run full pipeline, compare results against Go oracle

---

## Milestone 10 — Edge Cases & Completeness

- [ ] String-as-boolean (`Str → Bool(false)`) — `strings.fspec`
- [ ] History references across rounds — `history1-4.fspec`
- [ ] Stock swaps — `swaps/` directory
- [ ] Multi-file imports — `imports/` directory
- [ ] Bad spec error reporting — `badspecs/` directory
- [ ] Boolean stocks — `booleans.fspec`
- [ ] Indexes — `indexes.fspec`
- [ ] `bathtub2.fspec` (multiple parallel flows)
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
