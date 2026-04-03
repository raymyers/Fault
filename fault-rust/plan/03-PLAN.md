# Fault Rust — Phase 3: Quality, Coverage & Mutation Hardening

Improve correctness confidence, maintainability, and test quality of the Rust implementation.
Informed by branch coverage (84.8% baseline), mutation testing, Clippy analysis, and
[rust-skills](https://github.com/leonardomso/rust-skills) rules.

**Status (2026-04-03):** 167 tests pass. All 7 external examples correct.
Baseline metrics: 84.8% line coverage · 90.4% function coverage · Clippy: ~28 warnings.

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

- [ ] **31a. Remove dead code** — delete `collect_modified_vars` and `collect_modified_in_stmt`
  (dead since `collect_modified_vars_deep` replaced them).
- [ ] **31b. Fix identical if-blocks** — `validate.rs:78-82` has two branches producing the same
  error. Collapse or distinguish.
- [ ] **31c. Collapse if-chains** — ~9 collapsible if statements in encode.rs / statechart.rs.
  Apply `cargo clippy --fix` then review.
- [ ] **31d. Remove redundant closures** — ~10 instances. Apply `cargo clippy --fix`.
- [ ] **31e. Fix too-many-arguments** — `encode_mixed_if_in_state` has 9 params. Introduce a
  struct for the context.
- [ ] **31f. Workspace-level Clippy lints** — add `[workspace.lints.clippy]` to root `Cargo.toml`:
  `correctness = "deny"`, `suspicious = "warn"`, `perf = "warn"`, `style = "warn"`.

---

## Milestone 32 — Production Error Handling

- [ ] **32a. Replace unwrap chains in statechart.rs** — 4 `strip_prefix().unwrap()` chains at
  lines 918, 953, 976, 1015. Use `if let` or safe string manipulation.
- [ ] **32b. Replace panic! in resolve** — `lib.rs:592` ("expected FlowAssign") and `:744`
  ("expected Assert") should return `Result` or use `debug_assert!`.
- [ ] **32c. Replace panic! in statechart** — `statechart.rs:1086` (`cond_expr_to_smt` unhandled
  variant). Add a catch-all that returns a descriptive error string.
- [ ] **32d. Introduce `thiserror` error types for library crates** — at minimum for
  `fault_syntax` (ParseError) and `fault_resolve` (ResolveError). Track as stretch goal.

---

## Milestone 33 — Test Coverage Gaps (Target: 90%+ line coverage)

Priority ordered by risk (lowest coverage × highest criticality):

- [ ] **33a. fault_cli/main.rs (0%)** — Extract pipeline logic from main into a library function
  `run(args) -> Result<Output>` so it can be unit-tested without `process::exit`.
  Add 5–8 tests covering: smt mode, check mode, parse mode, system file, error paths.
- [ ] **33b. fault_syntax/parser.rs (80.2%)** — Add fixture tests for uncovered parser branches:
  error recovery paths, edge-case tokens (empty bodies, trailing commas, malformed imports).
  Target: 88%+.
- [ ] **33c. fault_exec/lib.rs (84.3%)** — Cover untested execution paths: nested if-else in
  exec, parallel with errors, unknown function calls.
- [ ] **33d. fault_resolve/loader.rs (77.4%)** — Test missing-file error path, circular import
  detection, relative path resolution edge cases.
- [ ] **33e. fault_smt/encode.rs (85.9%)** — Cover uncovered branches: target swaps (line 120),
  property overrides (line 130), const bool encoding (line 274), mixed-system
  run-if paths. Add fixture `.fspec` files that exercise these.
- [ ] **33f. fault_syntax/lexer.rs (85.3%)** — Test error recovery: unterminated strings,
  invalid number literals, unexpected characters.

---

## Milestone 34 — Mutation Hardening (Critical Modules)

Use `cargo mutants --file <path>` to identify surviving mutations, then add tests
that kill them. Focus on modules where a surviving mutation would produce wrong SMT.

- [ ] **34a. fault_smt/ssa.rs** — 14/27 missed (48% mutation score). Key survivors:
  `current_ro`, `snapshot`, `restore`, `merge_max`, `set_version`, `has`.
  Add direct unit tests for snapshot/restore round-trip, merge semantics, has-after-bump.
- [ ] **34b. fault_resolve/validate.rs** — 9/23 missed (57% caught). Key survivors:
  identical-block logic (line 78 `||` → `&&`), `check_double_swaps` guard conditions.
  Add badspec fixture tests that distinguish the two branches.
- [ ] **34c. fault_smt/encode.rs (targeted)** — run mutants on `encode_invariants`,
  `encode_temporal`, `encode_expr_at_round` (critical for correctness). Add assertion-heavy
  fixture tests.
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
