# Phase 4 — Friendly Counterexample Output

## Goal
When `fault-rust -m check` finds a counterexample (Z3 returns `sat`), display
a human-readable variable timeline instead of raw `(define-fun …)` S-expressions.

Mirror the spirit of the Go implementation's `Logger.Print()` output:
- Group SSA variables by base name
- Show values ordered by round (SSA index)
- Show transitions (old → new) when a value changes
- Filter internal solver variables (`@__run`, `block*true`, `block*false`)
- Print spec-relative names (strip `specname_` prefix)

## Milestones

### M41 — Parse Z3 model output
- **M41a**: Add `z3_parse` module to `fault_cli` with `parse_model(raw: &str) -> BTreeMap<String, String>`
  that extracts `(define-fun name () Type value)` → `name → value_string`.
- **M41b**: Unit tests: simple reals, bools, negative values, S-expr values like `(/ 5.0 2.0)`, `(- 1.0)`.

### M42 — Format friendly display
- **M42a**: Add `format_counterexample(model: &BTreeMap<String, String>, spec_name: &str) -> String`.
  - Strip spec prefix from variable names.
  - Group by base name (strip trailing `_N` SSA index).
  - Sort groups alphabetically, SSA indices numerically within each group.
  - Show `variable_name` header, then indented `  step N: value` lines.
  - Omit unchanged consecutive values (show `→` transitions only).
  - Filter internal variables.
- **M42b**: Unit tests for formatting: multi-var, bools, unchanged filtering, internal var filtering.

### M43 — Integrate into CLI
- **M43a**: Replace raw model dump in `run_check` with `format_counterexample`.
- **M43b**: Add `--raw` flag to preserve raw Z3 output for debugging.
- **M43c**: Integration tests with Z3 (gated behind `cfg(feature = "z3-tests")` or env var check).

### M44 — Polish
- **M44a**: Clippy clean, cargo test --all passes.
- **M44b**: Update 04-PLAN.md with final status.

## Status

| Milestone | Status |
|-----------|--------|
| M41 — Parse Z3 model | ✅ Done |
| M42 — Format friendly display | ✅ Done |
| M43 — Integrate into CLI | ✅ Done (`--raw` flag added) |
| M44 — Polish | ✅ Done (207 tests, 0 clippy warnings) |

### Test count: 207 (up from 191 before Phase 4)
### New tests: 16 in `z3_parse` module
