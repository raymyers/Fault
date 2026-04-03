# How To Make Progress — Phase 2

You are closing gaps between the Rust and Go Fault CLIs.
This file is everything you need to pick up the next task and finish it correctly.

**Current state (2026-04-03):** 158 tests pass. 6 of 7 external examples work. The one remaining major gap is **M17 — flow instances in mixed statechart+flow `.fsystem` files** (`repl.fsystem`).

---

## 1. Orient Yourself

### What this phase is about

Phase 1 (01-PLAN) built the Rust compiler from scratch.
Phase 2 (this plan) fixes every divergence found when running real-world examples through both CLIs.

**What's done:** M11 (lexer/parser), M12 core (SMT encoding), M13a (check mode guard). All single-spec `.fspec` files and pure-statechart `.fsystem` files produce correct results.

**What's left:** M17 (flow instances in mixed fsystem), M14 (formalize fixture tests), M15 (CLI polish), M16 (fixture regen), plus cosmetic M12c/d.

### Key Paths

| Path | What |
|------|------|
| `fault-rust/plan/02-PLAN.md` | Master plan — milestones, checkboxes, results table |
| `fault-rust/plan/02-SEED.md` | Discovery report: what was tested, what broke, root causes |
| `fault-rust/fault_smt/src/encode.rs` | **Primary file for M17.** SMT encoder — flows, ITE, assertions, `encode_expr_at_round` |
| `fault-rust/fault_smt/src/statechart.rs` | Statechart encoder — state functions, advance, stay |
| `fault-rust/fault_resolve/src/lib.rs` | Resolver — `resolve_system()` builds `ResolvedProgram` from `.fsystem` |
| `fault-rust/fault_smt/src/ssa.rs` | SSA versioning — `bump()`, `current()`, `has()` |
| `fault-rust/fault_syntax/src/parser.rs` | Parser — AST types including `System`, `Global`, `Component` |
| `fault-rust/fault_syntax/src/ast.rs` | AST node definitions |
| `fault-rust/fault_cli/src/main.rs` | CLI entry point |
| `fault-rust/testdata/` | Internal test fixtures |

### Build & Test Commands

```sh
# Rust CLI (from fault-rust/)
cargo build --release        # Binary: target/release/fault_cli
cargo test                   # 158 tests across all crates
cargo clippy -- -D warnings  # Lint check (matches CI)

# Go oracle (pre-compiled binary at repo root)
./fault-go -m smt -f path/to/input.fspec   # Generate SMT
./fault-go -f path/to/input.fspec           # Check mode (needs SOLVERCMD=z3 SOLVERARG="-in")

# Rust check mode (auto-discovers z3 in PATH)
./target/release/fault_cli -f path/to/input.fspec

# Side-by-side comparison
diff <(./fault-go -m smt -f FILE 2>&1) <(./target/release/fault_cli -m smt -f FILE 2>&1)
```

**Note:** The Go binary requires `SOLVERCMD=z3 SOLVERARG="-in"` env vars for check mode. The Rust binary auto-discovers `z3` in PATH. Install Z3 via `pip install z3-solver` (puts binary at `~/.local/bin/z3`).

---

## 2. Pick the Next Task

1. Open `fault-rust/plan/02-PLAN.md`.
2. **Priority order:** M17 (major gap) → M14 (fixture tests) → M13b → M15 → M12c/d/M16 (cosmetic).
3. Within a milestone, pick the **first unchecked bullet**.
4. That is your task. Do only that task.

The highest-impact next task is **M17a** — flow instance stock variable initialization in mixed fsystem.

---

## 3. Work Loop

```
READ    → Read the task bullet in 02-PLAN.md.
          Read the corresponding Rust source file(s).
          If the task involves Go behavior, diff Go vs Rust SMT output for the example.
          For M17: study how the Go encoder handles `global` declarations and
          flow function calls inside state bodies.

TEST    → Write or update a failing test FIRST.
          For SMT output tasks: generate expected.smt2 from Go oracle, commit it.
          For check-mode tasks: add an e2e test that runs through Z3.

FIX     → Implement the minimum code change to pass the test.
          cargo build && cargo test && cargo clippy

VERIFY  → Run the specific external example through the Rust CLI and confirm
          it now matches Go behavior.
          Run ALL tests to check for regressions: cargo test
          For M17: compare `repl.fsystem` SMT output line count and declarations
          against Go (target: ~218 lines, ~79 declarations).

COMMIT  → Single-purpose commit. Message format:
            M<n><letter>: <short description>
            e.g. "M17a: Initialize flow instance stock variables in fsystem"

UPDATE  → Tick the checkbox in 02-PLAN.md. Commit that too.
```

---

## 4. Test Conventions

### New fixture layout (external examples)

```
fault-rust/testdata/examples/<name>/
  input.fspec            # or input.fsystem (copied from Fault-lang/examples)
  expected.smt2          # Go oracle: fault-go -m smt -f input.fspec
  expected.check         # (optional) "sat" or "unsat" — Go check-mode result
```

### Rules

- Every fix gets at least one test that previously failed.
- Tests diff Rust output against oracle fixtures OR check sat/unsat result.
- For cosmetic diffs (block naming, declaration order): tests must compare *structurally* not textually — or the expected fixture must be regenerated to match Rust's output format after alignment.
- If Go also fails on an example (e.g. `drone.fsystem` — Go panics), mark the test `#[ignore]` with a comment explaining why.

---

## 5. Definition of Done

A task is **done** when ALL of:

- [ ] The specific failing example/fixture now works correctly.
- [ ] At least one new or updated test covers the fix.
- [ ] `cargo test` — all tests pass (0 failures).
- [ ] `cargo clippy -- -D warnings` — no warnings.
- [ ] Committed with clear message.
- [ ] Checkbox ticked in 02-PLAN.md.

---

## 6. Milestone-Specific Guidance

### M17 — Flow Instances in Mixed fsystem (HIGHEST PRIORITY)

This is the only remaining major gap. `repl.fsystem` combines statecharts (components with states) and flows (imported from `cache.fspec` and `orchestrator.fspec`) via `global` declarations. The Rust encoder handles statecharts correctly but does not encode the flow side.

**The problem in concrete terms:**

`repl.fsystem` declares:
```
global record = new cache.record;
global manager = new orchestrator.control;
```

State functions then invoke flow functions:
```
lookupRecord: func{
    record.lookup;          // ← calls cache.record.lookup flow function
    advance(this.returnRecord) || advance(this.createRecord);
}
```

Go output has 79 `declare-fun` lines (28 statechart + 51 flow stock variables).
Rust output has only 28 `declare-fun` lines (statechart only — flow variables are missing).

**17a — Flow instance stock variable initialization:**

Where to look:
- `fault_resolve/src/lib.rs` → `resolve_system()` (line ~350). Currently converts `global` declarations to `init_block` statements like `fl = new record`. The resolver merges stocks from imported specs via `merge_stocks()`, but the encoder may not be initializing them.
- `fault_smt/src/encode.rs` → `encode_mixed_system()` or equivalent top-level system encoder. It encodes statechart components but doesn't declare/initialize the stock variables that belong to flow instances.

What to do:
1. After encoding statechart state variables, iterate over the flow instances (from `global` declarations).
2. For each flow instance, look up the flow's stocks from the resolved program.
3. Declare and initialize each stock variable with the `spec_name_` prefix (e.g., `repl_record_machine_blocks_0`).

**17b — Flow function dispatch in state bodies:**

Where to look:
- `fault_smt/src/statechart.rs` → `encode_state_func()` or the function that encodes statements within state function bodies. When it encounters a statement like `record.lookup`, it needs to recognize this as a flow function call and inline the function body.
- `fault_smt/src/encode.rs` → `resolve_flow_stmt()` already handles flow function dispatch for `for N run` blocks. The same logic needs to work inside state function bodies, but with the flow instance name resolved to the correct flow definition.

What to do:
1. In the state-body encoder, detect statements that are flow function calls (Dot expressions like `record.lookup`).
2. Resolve the flow function name: `record` → `cache.record` flow def → `lookup` function.
3. Inline the function body using the existing `encode_flow_assign()` / `resolve_flow_stmt()` infrastructure.
4. All emitted assignments must be under the current state-active ITE guard.

**17c — Imported assertion propagation:**

The `cache.fspec` and `orchestrator.fspec` assertions must be included in `repl.fsystem`'s invariant set. Check `resolve_system()` — it calls `merge_invariants()` to collect assertions from imports. Verify they end up in the `ResolvedProgram.invariants` with correct variable qualification (the `spec_name_` prefix must be `repl_` not `cache_`).

**Techniques already proven in prior fixes:**

- `encode_expr_at_round()` auto-qualifies unresolved names with `spec_name_` prefix (commit `41fc5da`). This handles assertion variables.
- `collect_modified_vars_deep()` resolves Call statements through flow function bodies for ITE tracking (commit `f360486`). Use similar logic for state-body flow dispatch.
- `read_current()` falls back to `spec_name_` prefix when SSA lookup fails (commit `f360486`).

### M12c/d (Cosmetic — LOW PRIORITY)

- **12c (block numbering)**: `encode.rs` block-ID generation uses a shared counter. Go uses different counters per context. Purely cosmetic — does not affect solver results.
- **12d (declaration order)**: Different iteration order over internal data structures. Purely cosmetic.

Only tackle these after M17 is complete and all examples pass.

### M13b (Temporal encoding verification)

`orchestrator.fspec` returns CORRECT, so the temporal encoding likely works. The known difference is granularity: Go includes ALL intermediate SSA versions in temporal disjunctions; Rust only includes round-boundary snapshots. Verify this doesn't cause false negatives on new examples. If it does, the fix is in `encode_temporal_negated()` / `encode_temporal()` — iterate all SSA versions for each variable, not just round entries.

### M14 (Fixture Tests)

Formalize the manual verification into automated tests. Copy examples from `Fault-lang/examples` into `testdata/examples/` and add fixture-based integration tests. This is infrastructure work — do after M17 when the results are stable.

### M15 (CLI Feature Parity)

Quick wins: mode aliases (15a), SOLVERCMD validation (15b). Larger efforts: human-readable output (15c), reachability (15d). Do after M17.

---

## 7. Quick Diagnosis Cheat-Sheet

| Symptom | Likely cause | Where to look |
|---------|-------------|---------------|
| Missing `declare-fun` for flow stock variables in fsystem | Flow instances not initialized | `encode.rs` system encoder + `resolve/lib.rs` `resolve_system()` |
| Flow function call ignored in state body | State encoder doesn't dispatch flow calls | `statechart.rs` state-body encoder |
| `repl.fsystem` says COUNTEREXAMPLE (should be CORRECT) | Missing flow encoding → incomplete model | M17a + M17b + M17c |
| Assertion references unqualified variable in fsystem | `encode_expr_at_round` not qualifying | `encode.rs` ~line 1120 (auto-qualification with `spec_name_`) |
| Assertion encoding uses wrong operator (`not (<` vs `>=`) | Style difference, not a bug | Logically equivalent — no fix needed |
| Block numbering differs from Go | Counter scheme for ITE booleans | `encode.rs` block-ID generation (cosmetic) |
| Declaration order differs from Go | Iteration order difference | `encode.rs` / `statechart.rs` (cosmetic) |

---

## 8. Go Reference Code Pointers (for M17)

The Go encoder's handling of mixed statechart+flow systems is spread across:

| Go package | What it does |
|-----------|--------------|
| `generator/unpack/` | Expands flow function calls, resolves `new` instances |
| `generator/scenario/` | Builds the scenario tree with branch selectors and ITE blocks |
| `generator/smt/` | Emits SMT-LIB2 from the scenario tree |
| `execute/` | Orchestrates parse → resolve → encode → solve pipeline |

Key function: `unpack.go:unpackRule()` → when it encounters a flow function call in a state body, it inlines the function and wraps it in the state's ITE guard. This is the pattern to replicate in the Rust `statechart.rs` / `encode.rs`.
