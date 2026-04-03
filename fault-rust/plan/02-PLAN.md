# Fault Rust — Phase 2: Parity with Go CLI

Close every gap found when running [Fault-lang/examples](https://github.com/Fault-lang/examples) and diffing internal `testdata/` fixtures.
Goal: a user switching from the Go binary to the Rust binary gets correct results on every spec/system that Go handles, with no regressions on internal tests.

---

## Principles (inherited from 01-PLAN, plus)

1. **Fix semantics first, cosmetics later.** A wrong answer is worse than ugly output.
2. **One fix, one test, one commit.** Each task below gets at least one data-driven test that fails before the fix and passes after.
3. **Regenerate fixtures from Go oracle when needed.** If an expected file is stale or malformed (e.g. single-line blobs in `conditionals/`), regenerate it and commit the clean version *before* fixing Rust.
4. **External examples are first-class tests.** Copy the Fault-lang/examples into `testdata/examples/` and add fixture tests for them.

---

## Milestone 11 — Lexer & Parser Fixes

- [ ] **11a. Dot-prefix float literals** — `.15` must lex as `FloatLit("0.15")`.
  - In `fault_syntax/src/lexer.rs`, when `peek() == b'.'` and `peek_at(1).is_ascii_digit()`, enter `lex_number`.
  - Add lexer test: `.15`, `.5`, `.0`.
  - Unblocks: `battery.fspec`, `cache_unkn.fspec`.

- [ ] **11b. Bare constant declarations** — `const name;` (no `= value`) must produce a `ConstDef` with `value: Unknown` (or a new `Val::Uninitialized`).
  - In `fault_syntax/src/parser.rs`, the `parse_const` path that sees `;` immediately must still push a `ConstDef`.
  - Add parser test: `const table; const memory;` → two constants in the AST.
  - Unblocks: `cache_unkn.fspec`.

- [ ] **11c. Spec-only files with const expressions** — `strings2/input.fspec` has top-level `name = expr;` statements and no run block. The pipeline should still encode these.
  - The resolver + SMT encoder must handle specs where `run_block` is `None` but constants with expressions exist.
  - Add fixture test: `strings2` must produce the expected SMT (currently errors "nothing to run").

---

## Milestone 12 — SMT Encoding Correctness

- [ ] **12a. Complete `cond_expr_to_smt`** — handle all `BinOp` variants (`Eq`, `Lt`, `Gt`, `Le`, `Ge`, `Neq`) and `Lit(Nat(_))` / `Lit(Float(_))` in statechart condition expressions.
  - In `fault_smt/src/statechart.rs`, extend `cond_expr_to_smt` match arms.
  - Remove the `UNHANDLED_COND` fallback (make it a compile error or explicit panic with context).
  - Test: the `drone.fsystem` condition `nav.pos.z == 0` must produce valid SMT.

- [ ] **12b. Run-block conditional gating** — `if cond { side_effects }` in a `for N run { ... }` block must wrap side effects in an `ite`, not execute them unconditionally.
  - Root cause: the SMT encoder emits the side-effect assignments but does not wrap them in the block's boolean gate.
  - Verify by diffing `orchestrator.fspec` Rust SMT output against Go oracle output. The `cluster.remove` must be conditional on `instances > 1`.
  - Test: `orchestrator.fspec` check mode must return "CORRECT" (no counterexample), matching Go.

- [ ] **12c. Block numbering alignment** — Rust uses `block{N}true_{round}` / `block{N}false_{round}` with a shared counter. Go uses separate counters for true/false branches. Align to match Go oracle output.
  - Audit `fault_smt/src/encode.rs` block-ID generation.
  - Regenerate and update all internal `expected.smt2` fixtures after the change.
  - Test: all internal fixture tests still pass.

- [ ] **12d. Statechart declaration ordering** — Rust emits `declare-fun` lines in a different order than Go for statecharts. Align emission order (or normalize both for comparison).
  - Low priority if tests compare structurally. Skip if fixture tests already pass.

---

## Milestone 13 — Check Mode Correctness

- [ ] **13a. No-assertion guard** — when a spec has zero assertions, the check mode should report "no assertions to check" instead of "COUNTEREXAMPLE FOUND".
  - Before appending `(check-sat)`, inspect whether any `(assert (not ...))` or `(assert (or (not ...)))` assertion-negation lines were emitted. If none, skip solver and report accordingly.
  - Test: `fibonacci.fspec` in check mode → "no assertions to check" (not "COUNTEREXAMPLE FOUND").

- [ ] **13b. `eventually-always` temporal encoding in fspec run blocks** — verify the Rust encoding of `assert X eventually-always` matches Go when used in a `for N run` spec (not system).
  - Diff `orchestrator.fspec` SMT temporal suffix against Go oracle.
  - Test: `orchestrator.fspec` produces correct temporal assertion encoding.

---

## Milestone 14 — External Examples as Fixtures

- [ ] **14a. Import Fault-lang/examples into testdata** — copy each example into `testdata/examples/<name>/` with `input.fspec` (or `.fsystem`) and `expected.smt2` from Go oracle.
  - `testdata/examples/fibonacci/`
  - `testdata/examples/sandwich/`
  - `testdata/examples/cache/`
  - `testdata/examples/cache_unkn/`
  - `testdata/examples/orchestrator/`
  - `testdata/examples/repl_system/`
  - For `battery.fspec`, `position.fspec`: Go also fails, so skip or mark as `#[ignore]`.
  - For `drone.fsystem`: Go also panics, so skip or mark as `#[ignore]`.

- [ ] **14b. Add fixture tests for external examples** — write tests that parse + encode each example and diff against `expected.smt2`.
  - These tests should fail initially, then pass as Milestones 11-13 are completed.

- [ ] **14c. Add end-to-end check-mode tests** — for examples with assertions, run through Z3 and verify the sat/unsat result matches Go.
  - `sandwich.fspec` → unsat (CORRECT)
  - `orchestrator.fspec` → unsat (CORRECT)
  - `repl.fsystem` → unsat (CORRECT)
  - `cache.fspec` → sat (counterexample found)

---

## Milestone 15 — CLI Feature Parity

- [ ] **15a. Mode name aliases** — accept `-m model` as alias for `-m check`, and `-m ast` as alias for `-m parse`, for Go CLI compatibility.

- [ ] **15b. SOLVERCMD/SOLVERARG validation** — when SOLVERCMD or SOLVERARG is unset and mode is `check`, print a helpful message and fall back to `smt` output (matching Go behavior).

- [ ] **15c. Human-readable result output** — when check mode finds a counterexample, parse the Z3 model and produce a structured trace (round-by-round variable changes) instead of raw S-expression dump.
  - This is the Go `execute/responses.go` + `generator/scenario/` functionality.
  - May be deferred to a future milestone if complex; document the gap.

- [ ] **15d. `-complete` flag (reachability checking)** — implement basic reachability analysis matching Go's `reachability/` package.
  - May be deferred; document the gap.

- [ ] **15e. `-i` input format flag** — accept `-i fault` (default), `-i ll`, `-i smt2`.
  - `-i ll` and `-i smt2` may be stubs that print "not yet supported"; document.

- [ ] **15f. `-output` format flag** — accept `-output text` (default) and `-output smt`.

---

## Milestone 16 — Fixture Cleanup & Regen

- [ ] **16a. Regenerate conditional fixtures** — the `testdata/conditionals/*.smt2` files are single-line blobs from Go. Regenerate them properly with the Go binary and commit.

- [ ] **16b. Update all expected.smt2 after block-numbering fix** — once 12c lands, re-run `oracle.sh` (or equivalent) for every fixture and commit updated expected files.

- [ ] **16c. Verify all 156+ tests pass** — final confirmation that nothing regressed.

---

## Dependency Graph

```
M11 (lexer/parser fixes)
  ├──→ M12 (SMT encoding correctness)  ──→ M13 (check mode correctness)
  │                                              │
  └──→ M14 (external examples as fixtures) ──────┘
                                                  │
                                            M15 (CLI feature parity)
                                                  │
                                            M16 (fixture cleanup)
```

M11 is prerequisite for everything.
M12 and M14 can proceed in parallel after M11.
M13 depends on M12.
M15 and M16 are independent polish tasks.
