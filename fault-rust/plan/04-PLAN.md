# Phase 4 — Friendly Counterexample Output (Redo)

## Goal
When `fault-rust -m check` finds a counterexample, display human-readable
round-based output matching the Go implementation's `Logger.Print()` format:
function call nesting, variable transitions ("Set variable X to value Y",
"X: old → new", "Variable X is still Y"), proper indentation.

## Architecture

1. **Event logging** (`fault_smt/src/event_log.rs`): The SMT encoder records
   events during encoding: `RunStart`, `FunctionEntry`, `FunctionExit`,
   `VariableUpdate`, `Solvable`.

2. **Encoder instrumentation** (`fault_smt/src/encode.rs`):
   - `encode_program_with_log()` returns `(String, EventLog)`
   - `encode_round()` tracks `current_round`
   - `encode_call()` logs FunctionEntry/Exit
   - `encode_flow_assign()` logs VariableUpdate

3. **Formatter** (`fault_cli/src/z3_parse.rs`):
   - `format_from_event_log()` — replays event log with Z3 results (Go-style)
   - `format_counterexample_flat()` — flat SSA timeline fallback
   - `format_counterexample()` — dispatches: uses event log when it has real
     content, falls back to flat for constants-only/statechart specs

## Milestones

### M41 — Event log infrastructure
- **M41a**: `EventLog` struct and `Event` enum in `fault_smt/event_log.rs`
- **M41b**: `encode_program_with_log()` returns `(String, EventLog)`
- **M41c**: Instrument `encode_round`, `encode_call`, `encode_flow_assign`

### M42 — Go-style formatter
- **M42a**: `format_from_event_log()` replaying events with indent tracking
- **M42b**: Three display modes: "Set variable X to value Y" (first time),
  "X: old → new" (transition), "Variable X is still Y" (unchanged)
- **M42c**: Internal variable filtering, solvable resolution display
- **M42d**: Flat fallback for specs without function calls

### M43 — CLI integration
- **M43a**: `run_check()` uses `encode_program_with_log`, passes event log
- **M43b**: `--raw` flag for raw Z3 model output
- **M43c**: Smart dispatch: event log for flow specs, flat for constants/statecharts

### M44 — Tests
- Parser tests: reals, bools, division, negation, actual Z3 output
- Internal filter tests: @__run, block selectors, normal vars
- Event log replay: set variable, transition, still, indentation, filtering, solvable
- Flat fallback: basic, unchanged skipping
- Integration dispatch: event log vs flat fallback

## Status

| Milestone | Status |
|-----------|--------|
| M41 — Event log | ✅ Done |
| M42 — Go-style formatter | ✅ Done |
| M43 — CLI integration | ✅ Done |
| M44 — Tests | ✅ Done |

### Test count: 212 (21 new: 1 in event_log, 20 in z3_parse)
### Clippy: 0 warnings

### Verified specs:
- `asserts/input.fspec` → round-based with transitions
- `unknowns/input.fspec` → round-based with function calls
- `cache/cache.fspec` → multi-round, multiple vars, transitions+still
- `cache_unkn/cache_unkn.fspec` → unknown variables, round-based
- `strings/input.fspec` → flat fallback (no run block)
- `drone/drone.fsystem` → "All good!" (unsat)
- `orchestrator/orchestrator.fspec` → "All good!" (unsat)
- `sandwich/sandwich.fspec` → "All good!" (unsat)
