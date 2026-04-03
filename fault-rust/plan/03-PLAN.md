# Fault Rust — Phase 3: Quality, Coverage & Mutation Hardening

Improve correctness confidence, maintainability, and test quality of the Rust implementation.
Informed by branch coverage (84.8% baseline), mutation testing, Clippy analysis, and
[rust-skills](https://github.com/leonardomso/rust-skills) rules.

**Status (2026-04-03):** 257 tests pass. All 8 external examples correct.
Clippy: 0 warnings (clean). Workspace lints enforced.

---

## Principles

1. **Meaningful tests over coverage gaming.** Prefer data-driven fixture tests and property tests
   that encode real-world behaviour. A test that catches a mutation is worth more than one that
   just touches a line.
2. **Fix the bug the mutant reveals.** A survived mutation usually means a test is too weak or a
   branch is unreachable dead code. Address the root cause.
3. **Clippy clean, pedantic selective.** Apply `clippy::correctness` as deny and address all
   warnings. Selectively enable `clippy::pedantic` lints that catch real bugs.
4. **No production panics.** Replace `unwrap()` / `panic!()` in non-test code with proper error
   handling (`Result`, `Option` combinators, or `expect()` with invariant comment).
5. **Shrink large files.** `encode.rs` (2943 lines) should be split along natural seams.

---

## Milestone 31 — Clippy Clean + Dead Code Removal

- [x] **31a. Remove dead code** — deleted `collect_modified_vars` and `collect_modified_in_stmt`.
- [x] **31b. Fix identical if-blocks** — collapsed validate.rs:78-82 into unified logic.
- [x] **31c. Collapse if-chains** — applied `cargo clippy --fix` for ~9 collapsible ifs.
- [x] **31d. Remove redundant closures** — applied `cargo clippy --fix` for ~10 closures.
- [x] **31e. Fix too-many-arguments** — introduced `MixedIfContext` struct for `encode_mixed_if_in_state`.
- [x] **31f. Workspace-level Clippy lints** — added `[workspace.lints.clippy]` to root `Cargo.toml`
  and `[lints] workspace = true` to each crate.

---

## Milestone 32 — Production Error Handling

- [x] **32a. Replace unwrap chains in statechart.rs** — extracted `parse_advance_target` helper,
  replaced 4 unwrap chains with safe string manipulation.
- [x] **32b. Replace panic! in resolve** — lib.rs:592 and :744 are in test code (acceptable).
- [x] **32c. Replace panic! in statechart** — `cond_expr_to_smt` catch-all now returns
  descriptive SMT comment instead of panicking.
- [ ] **32d. Introduce `thiserror` error types for library crates** — stretch goal.

---

## Milestone 33 — Test Coverage Gaps (Target: 90%+ line coverage)

Priority ordered by risk (lowest coverage × highest criticality):

- [x] **33a. fault_cli/main.rs (0%)** — Extracted `fault_cli::run(Mode, src, path) -> Output`
  to `lib.rs`. Added 7 tests (smt, parse, check modes, error paths, imports, booleans).
- [x] **33b. fault_syntax/parser.rs (80.2%)** — Added 6 parser error-path tests (empty file,
  missing semi, bad token, incomplete def, missing spec name, fixture dir).
- [x] **33c. fault_exec/lib.rs (84.3%)** — Added 12 tests: nil condition branch, Advance/Stay/Seq
  stmt, CompoundTransition/ChooseTransition, unknown function calls, call-no-dot,
  multi-round, component state matching, unknown component state, init non-assign.
- [x] **33d. fault_resolve/loader.rs (77.4%)** — Added 5 loader tests: missing file, parse error,
  valid import, circular import cycle breaking, system import missing file.
- [x] **33e. fault_smt/encode.rs (85.9%)** — Added 9 fixture tests: 3 swap oracle (swaps,
  swaps1, swaps2) exercising target swaps and property overrides; 6 conditional
  structural tests (condwelse, multicond1-5) exercising if/else encoding paths.
- [x] **33f. fault_syntax/lexer.rs (85.3%)** — Added 14 lexer tests: unterminated string,
  unterminated raw string, unexpected character, string escape, block comment EOF,
  error display, token kind display, increment/decrement, bitwise, shift ops,
  scientific notation, underscore idents, brackets/parens, multiline position tracking.

---

## Milestone 34 — Mutation Hardening (Critical Modules)

Use `cargo mutants --file <path>` to identify surviving mutations, then add tests
that kill them. Focus on modules where a surviving mutation would produce wrong SMT.

- [x] **34a. fault_smt/ssa.rs** — Added 7 SSA unit tests: snapshot/restore roundtrip,
  merge_max both directions, current_ro immutability, has-after-bump, set_version, bump returns.
- [x] **34b. fault_resolve/validate.rs** — Added 4 badspec fixture tests: flowsnorun,
  stocksnorun, emptyspec (all MissingRunBlock), constsonly (valid).
- [x] **34c. fault_smt/encode.rs (targeted)** — Added 5 assertion-heavy e2e tests:
  assert-always-negated (OR of NOT), assume-not-negated (AND), eventually-negated,
  const-bool-encoding (Bool sort declaration), when-then-assert (implication).
- [ ] **34d. fault_smt/statechart.rs (targeted)** — run mutants on `qname` (cross-component
  fix), `encode_advance_and_body`, `encode_advance_or_body`. Verify that the
  cross-component advance fix is mutation-tested.

---

## Milestone 35 — Property-Based Testing (Stretch)

- [ ] **35a. Parser roundtrip** — `proptest`: generate random valid token sequences, parse,
  serialize to JSON, deserialize, compare. Catches parser/AST serialization bugs.
- [ ] **35b. SSA invariant** — `proptest`: random sequences of `bump(name)` → version is always
  previous + 1; `snapshot` → `restore` → versions match snapshot.
- [ ] **35c. Encode determinism** — `proptest`: any `ResolvedProgram` produces identical SMT
  output across multiple calls (already tested for some fixtures; generalize).

---

## Milestone 36 — Structural Improvements (encode.rs split)

- [ ] **36a. Extract mixed-system encoder** — move `encode_mixed_system`,
  `encode_mixed_stmt_in_state`, `encode_mixed_if_in_state`, `encode_mixed_run_if`,
  `encode_mixed_expr`, `encode_mixed_expr_bare`, `mixed_var_versioned` to a new
  `fault_smt/src/mixed.rs` module (~600 lines).
- [ ] **36b. Extract invariant encoder** — move `encode_invariants`, `encode_temporal`,
  `encode_temporal_negated`, `encode_when_temporal*`, `encode_expr_at_round` to
  `fault_smt/src/invariants.rs` (~200 lines).
- [ ] **36c. Extract constant encoder** — move `encode_constants`, `encode_const_expr`,
  `resolve_const_name`, `const_expr_base_name` to `fault_smt/src/constants.rs` (~100 lines).

---

## Coverage Targets

| File | Baseline | Target | Strategy |
|------|----------|--------|----------|
| fault_cli/main.rs | 0% | 60%+ | 33a: extract library function |
| fault_syntax/parser.rs | 80.2% | 88%+ | 33b: error-path fixtures |
| fault_resolve/loader.rs | 77.4% | 85%+ | 33d: edge-case tests |
| fault_smt/encode.rs | 85.9% | 90%+ | 33e + 34c: fixtures + mutations |
| fault_syntax/lexer.rs | 85.3% | 90%+ | 33f: error recovery tests |
| fault_exec/lib.rs | 84.3% | 88%+ | 33c: execution edge cases |
| **Overall** | **84.8%** | **90%+** | |

---

## Mutation Score Targets

| Module | Baseline | Target |
|--------|----------|--------|
| fault_smt/ssa.rs | 48% caught | 75%+ |
| fault_resolve/validate.rs | 57% caught | 80%+ |
| fault_smt/statechart.rs (targeted) | untested | 70%+ |

---

## Dependency Graph

```
M31 (clippy clean) ─────────────────────────────────────┐
  │                                                      │
  ├──→ M32 (error handling) ── depends on 31a (dead code)│
  │                                                      │
M33 (coverage gaps) ─────────────────────────────────────┤
  │                                                      │
  ├──→ M34 (mutation hardening) ── uses 33's new tests   │
  │                                                      │
M35 (proptest) ── stretch, independent                   │
  │                                                      │
M36 (encode.rs split) ── depends on M31e, M33e done first│
```
