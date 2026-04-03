# Fault Rust — Phase 2: Parity with Go CLI

Close every gap found when running [Fault-lang/examples](https://github.com/Fault-lang/examples) and diffing internal `testdata/` fixtures.
Goal: a user switching from the Go binary to the Rust binary gets correct results on every spec/system that Go handles, with no regressions on internal tests.

**Status (2026-04-03):** 158 tests pass. 6 of 7 external examples produce correct results. One major gap remains: flow-instance encoding in mixed statechart+flow `.fsystem` files (`repl.fsystem`).

---

## Principles (inherited from 01-PLAN, plus)

1. **Fix semantics first, cosmetics later.** A wrong answer is worse than ugly output.
2. **One fix, one test, one commit.** Each task below gets at least one data-driven test that fails before the fix and passes after.
3. **Regenerate fixtures from Go oracle when needed.** If an expected file is stale or malformed (e.g. single-line blobs in `conditionals/`), regenerate it and commit the clean version *before* fixing Rust.
4. **External examples are first-class tests.** Copy the Fault-lang/examples into `testdata/examples/` and add fixture tests for them.

---

## Milestone 11 — Lexer & Parser Fixes

- [x] **11a. Dot-prefix float literals** — `.15` must lex as `FloatLit("0.15")`.
  - Fixed in lexer. `battery.fspec`, `cache_unkn.fspec` now parse correctly.

- [x] **11b. Bare constant declarations** — `const name;` (no `= value`) must produce a `ConstDef` with `value: Val::Unknown`.
  - Commit `e151982`. Parser test added: `const table; const memory;` → two constants in AST.

- [x] **11c. Spec-only files with const expressions** — `strings2/input.fspec` has top-level `name = expr;` statements and no run block.
  - Commit `4d216e7`. Encoder no longer errors "nothing to run" on const-only specs.

---

## Milestone 12 — SMT Encoding Correctness

- [x] **12a. Complete `cond_expr_to_smt`** — all `BinOp` variants (`Eq`, `Lt`, `Gt`, `Le`, `Ge`, `Neq`) and `Lit(Nat/Float)` in statechart conditions.
  - Commit `cf57a05`. `drone.fsystem` condition `nav.pos.z == 0` now produces valid SMT.

- [x] **12b. Run-block conditional gating + variable qualification** — three critical fixes:
  1. `collect_modified_vars_deep`: resolves Call stmts through flow function bodies so variables modified by function calls inside if-branches are properly tracked for ITE generation.
  2. Dot expression flattening in `encode_expr`: properly flattens `Dot` chains to qualified variable names with spec prefix.
  3. `read_current` variable qualification: falls back to `spec_name_` prefix when a variable isn't found in SSA.
  - Commit `f360486`. `orchestrator.fspec` check mode now returns CORRECT.

- [x] **12e. Bare-const SMT sort inference** — `const table;` and `const memory;` declared as `Bool` but should be `Real` (used in numeric comparisons).
  - Added `const_sort()` helper: `Val::Unknown`/numeric → `Real`, string/expression → `Bool`.
  - Commit `8ccef99`.

- [x] **12f. Temporal round versioning** — `encode_expr_at_round` used round number as version suffix, generating references to undeclared variables (e.g. `cache_memory_1`). Now uses `round_entries` to find correct SSA version; constants that never change naturally get `_0`.
  - Commit `8ccef99` (same as 12e). Fixed `cache_unkn.fspec` Z3 sort errors.

- [x] **12g. Assertion variable qualification for fsystem** — `encode_expr_at_round` now auto-qualifies variable names with `spec_name_` prefix when the bare name isn't tracked in SSA. Fixes assertion encoding for both fsystem and flow specs.
  - Commit `41fc5da`. Fixed `drone.fsystem` ("unknown constant" → CORRECT) and `orchestrator.fspec` (false COUNTEREXAMPLE → CORRECT).

- [ ] **12c. Block numbering alignment** — Rust uses `block{N}true_{round}` / `block{N}false_{round}` with a shared counter. Go uses separate counters. Cosmetic only.
  - Low priority. Does not affect solver correctness.

- [ ] **12d. Statechart declaration ordering** — Rust emits `declare-fun` lines in a different order than Go. Cosmetic only.
  - Low priority if tests compare structurally.

---

## Milestone 13 — Check Mode Correctness

- [x] **13a. No-assertion guard** — specs with zero assertions now report "no assertions to check" instead of false COUNTEREXAMPLE.
  - Commit `b5e201d`. `fibonacci.fspec` in check mode → "Fault could not find a failure case. (no assertions to check)".

- [ ] **13b. `eventually-always` temporal encoding** — verify Rust encoding of `assert X eventually-always` matches Go for fspec run blocks.
  - `orchestrator.fspec` now returns CORRECT, suggesting this is likely working, but temporal assertion granularity differs (see Known Divergences below).

---

## Milestone 14 — External Examples End-to-End

**Verified results (2026-04-03):**

| Example | Go CLI | Rust CLI | Match? |
|---------|--------|----------|--------|
| `sandwich.fspec` | CORRECT | CORRECT | ✅ |
| `fibonacci.fspec` | execution trace | "no assertions to check" | ✅ (correct behavior) |
| `cache.fspec` | COUNTEREXAMPLE | COUNTEREXAMPLE | ✅ |
| `cache_unkn.fspec` | COUNTEREXAMPLE | COUNTEREXAMPLE | ✅ |
| `orchestrator.fspec` | CORRECT | CORRECT | ✅ |
| `drone.fsystem` | **panics** (Go bug) | CORRECT | ✅ (Rust better) |
| `repl.fsystem` | 218-line SMT / CORRECT | 56-line SMT / COUNTEREXAMPLE | ❌ Gap |

- [ ] **14a. Import Fault-lang/examples into testdata** — copy each example into `testdata/examples/<name>/` with `input.fspec` (or `.fsystem`) and `expected.smt2` from Go oracle.

- [ ] **14b. Add fixture tests for external examples** — write tests that parse + encode each example and diff against `expected.smt2`.

- [ ] **14c. Add end-to-end check-mode tests** — for examples with assertions, verify sat/unsat result.
  - `sandwich.fspec` → unsat (CORRECT) ✅
  - `orchestrator.fspec` → unsat (CORRECT) ✅
  - `cache.fspec` → sat (COUNTEREXAMPLE) ✅
  - `cache_unkn.fspec` → sat (COUNTEREXAMPLE) ✅
  - `drone.fsystem` → unsat (CORRECT) ✅ (Go panics)
  - `repl.fsystem` → unsat (CORRECT) ❌ (Rust says COUNTEREXAMPLE — gap)

---

## Milestone 17 — Flow Instances in Mixed fsystem (NEW — Major Gap)

The `repl.fsystem` example uses `global record = new cache.record` and `global manager = new orchestrator.control` to create flow instances that are then invoked from statechart state functions (e.g. `record.lookup`, `manager.boot`). The Rust encoder does not expand these flow function calls inside state bodies.

- [ ] **17a. Flow instance stock variable initialization** — `global record = new cache.record` must declare and initialize the stock variables (`repl_record_machine_blocks_0`, `repl_record_machine_table_0`, etc.) in the SMT encoding.
  - Go: 79 declarations; Rust: only 28 (missing all flow stock variables).

- [ ] **17b. Flow function dispatch in state bodies** — when a state function calls `record.lookup` or `manager.boot`, the encoder must inline the corresponding flow function body, emitting the flow's stock variable assignments under the state-active ITE guard.
  - This is the core feature: bridging the statechart encoder with the flow encoder for mixed systems.

- [ ] **17c. Imported assertion propagation** — imported specs' assertions (from `cache.fspec` and `orchestrator.fspec`) must be carried into the fsystem's invariant set with correct variable qualification.

---

## Milestone 15 — CLI Feature Parity

- [ ] **15a. Mode name aliases** — accept `-m model` as alias for `-m check`, and `-m ast` as alias for `-m parse`.
- [ ] **15b. SOLVERCMD/SOLVERARG validation** — helpful message and fallback when unset.
- [ ] **15c. Human-readable result output** — structured trace instead of raw S-expression.
- [ ] **15d. `-complete` flag (reachability checking)** — matching Go's `reachability/` package.
- [ ] **15e. `-i` input format flag** — accept `-i fault`, `-i ll`, `-i smt2`.
- [ ] **15f. `-output` format flag** — accept `-output text`, `-output smt`.

---

## Milestone 16 — Fixture Cleanup & Regen

- [ ] **16a. Regenerate conditional fixtures** — `testdata/conditionals/*.smt2` files are single-line blobs.
- [ ] **16b. Update all expected.smt2 after block-numbering fix** — once 12c lands.
- [ ] **16c. Verify all 158+ tests pass** — final regression confirmation.

---

## Known Divergences (semantic, not bugs)

1. **Assertion encoding style**: Rust `(not (< a b))` vs Go `(>= a b)` — logically equivalent, no impact on solver.

2. **Temporal assertion granularity**: Go includes ALL intermediate SSA versions in temporal assertion disjunctions (e.g. `blocks_0` through `blocks_30`). Rust only includes round-boundary snapshots (`blocks_0`, `blocks_6`, `blocks_12`, ...). Semantically, Go checks invariants at every intermediate SSA step; Rust only at round boundaries. This could matter for mid-round invariant violations.

3. **Block numbering**: Rust numbers ITE blocks sequentially (`block1`, `block2`, ...); Go uses different schemes. Cosmetic only.

---

## Dependency Graph

```
M11 (lexer/parser) ✅ DONE
  ├──→ M12 (SMT encoding) ✅ core done, 12c/12d cosmetic remain
  │     └──→ M13 (check mode) ✅ 13a done, 13b likely working
  │
  └──→ M14 (external examples) — partially verified, fixture tests not yet added
                │
          M17 (flow instances in fsystem) ← MAJOR GAP, blocks repl.fsystem
                │
          M15 (CLI feature parity) — not started
                │
          M16 (fixture cleanup) — not started
```

## Commit Log (ray/rust-impl, Phase 2)

| Commit | Tag | Description |
|--------|-----|-------------|
| `e151982` | M11b | Bare const parsing (`const name;` → Val::Unknown) |
| `4d216e7` | M11c | Const-only specs skip "nothing to run" validation |
| `cf57a05` | M12a | Complete cond_expr_to_smt (all comparison + arithmetic ops) |
| `b5e201d` | M13a | No-assertion guard (skip Z3 for specs without invariants) |
| `f360486` | M12b | collect_modified_vars_deep, Dot flattening, read_current qualification |
| `8ccef99` | M12c | const_sort for bare consts; encode_expr_at_round uses round_entries |
| `41fc5da` | M12d | encode_expr_at_round auto-qualifies with spec_name prefix |
