# How To Make Progress — Phase 2

You are closing gaps between the Rust and Go Fault CLIs.
This file is everything you need to pick up the next task and finish it correctly.

---

## 1. Orient Yourself

### What this phase is about

Phase 1 (01-PLAN) built the Rust compiler from scratch.
Phase 2 (this plan) fixes every divergence found when running real-world examples through both CLIs.

### Key Paths

| Path | What |
|------|------|
| `fault-rust/plan/02-PLAN.md` | This phase's master plan — milestones and checkboxes |
| `fault-rust/plan/02-SEED.md` | Discovery report: what was tested, what broke, root causes |
| `fault-rust/testdata/` | Internal test fixtures (existing) |
| `fault-rust/testdata/examples/` | External examples from Fault-lang/examples (to be added) |
| `fault-rust/fault_syntax/src/lexer.rs` | Lexer — fix dot-prefix floats here |
| `fault-rust/fault_syntax/src/parser.rs` | Parser — fix bare constants here |
| `fault-rust/fault_smt/src/encode.rs` | SMT encoder for fspec run blocks |
| `fault-rust/fault_smt/src/statechart.rs` | SMT encoder for fsystem state charts |
| `fault-rust/fault_cli/src/main.rs` | CLI entry point |

### Build Commands

```sh
# Go oracle (from repo root)
go build -o fault-go .

# Rust CLI (from fault-rust/)
cargo build --release
# Binary: target/release/fault_cli

# Run Rust tests
cargo test

# Generate Go oracle SMT for a fixture
export SOLVERCMD=z3 SOLVERARG="-in"
./fault-go -m smt -f path/to/input.fspec > path/to/expected.smt2

# Run check mode
./fault-go -f path/to/input.fspec        # Go
./target/release/fault_cli -f path/to/input.fspec  # Rust
```

---

## 2. Pick the Next Task

1. Open `fault-rust/plan/02-PLAN.md`.
2. Find the **earliest milestone with an unchecked `[ ]` bullet**.
3. Within that milestone, pick the **first unchecked bullet** (task order is dependency order within a milestone).
4. That is your task. Do only that task.

---

## 3. Work Loop

```
READ    → Read the task bullet in 02-PLAN.md.
          Read the corresponding Rust source file(s).
          Read 02-SEED.md for context on the specific failure.
          If the task involves Go behavior, run the Go CLI to confirm expected output.

TEST    → Write or update a failing test FIRST.
          For SMT output tasks: generate expected.smt2 from Go oracle, commit it.
          For parser tasks: add a test case that parses the previously-failing input.
          For check-mode tasks: add an e2e test that runs through Z3.

FIX     → Implement the minimum code change to pass the test.
          cargo build && cargo test && cargo clippy && cargo fmt

VERIFY  → Run the specific external example through the Rust CLI and confirm
          it now matches Go behavior.
          Run ALL tests to check for regressions: cargo test

COMMIT  → Single-purpose commit. Message format:
            M<n><letter>: <short description>
            e.g. "M11a: Support dot-prefix float literals in lexer"

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
- If Go also fails on an example (drone.fsystem, battery.fspec without run block), mark the test `#[ignore]` with a comment explaining why.

---

## 5. Definition of Done

A task is **done** when ALL of:

- [ ] The specific failing example/fixture now works correctly.
- [ ] At least one new or updated test covers the fix.
- [ ] `cargo test` — all tests pass (0 failures).
- [ ] `cargo clippy` — no warnings.
- [ ] `cargo fmt` — clean.
- [ ] Committed with clear message.
- [ ] Checkbox ticked in 02-PLAN.md.

---

## 6. Milestone-Specific Guidance

### M11 (Lexer/Parser)

- **11a (dot-prefix floats)**: The fix is in `lexer.rs` around line 251. Currently the dispatch only enters `lex_number` when `ch.is_ascii_digit()`. Add a branch: if `ch == b'.' && peek_at(1).is_ascii_digit()`, also enter `lex_number`. Inside `lex_number`, handle the case where the first char is `.` (skip the integer-part loop, go straight to the decimal part).
- **11b (bare constants)**: In `parser.rs`, find where `const` is parsed. When the next token after the name is `;` (no `=`), push a `ConstDef { name, value: Val::Unknown, expr: None }`.
- **11c (strings2)**: The issue is that `encode_program` bails when there's no run block. It should still encode constant definitions with expressions. Check `fault_smt/src/encode.rs` for the early return.

### M12 (SMT Encoding)

- **12a (cond_expr_to_smt)**: In `statechart.rs`, the function at ~line 1024 needs match arms for `BinOp { op: Eq|Lt|Gt|Le|Ge|Neq, left, right }`. Each emits `(= left right)`, `(< left right)`, etc. Use `cond_expr_to_smt` recursively on left/right.
- **12b (run-block conditionals)**: The most impactful bug. The SMT encoder for `IfThenElse` in run blocks must emit an `ite` that gates all side effects. Compare `encode.rs` ITE encoding with how the Go `generator/` package emits ITE blocks. The Go version wraps both the true-branch effects AND the false-branch (no-op / carry forward) in the ITE.
- **12c (block numbering)**: Lower priority. The Go oracle uses different block-ID schemes per context. Align after correctness fixes, then regenerate all fixtures.

### M13 (Check Mode)

- **13a (no-assertion guard)**: In `main.rs` `run_check_mode`, after generating SMT, count how many assertion-negation lines were emitted. If zero, skip solver. Alternatively, check `resolved.invariants` for any `Assert` variants before calling the solver.
- **13b (eventually-always)**: Diff the temporal encoding suffix in `encode.rs` against Go oracle for `orchestrator.fspec`. The Go version emits a large `or(and(...))` disjunction; verify the Rust version matches.

### M15 (CLI)

- Mode aliases and flag validation are quick wins.
- Human-readable result output (15c) and reachability (15d) are larger efforts — implement stubs if needed, document as future work.

---

## 7. Quick Diagnosis Cheat-Sheet

| Symptom | Likely cause | Where to look |
|---------|-------------|---------------|
| `parse error: expected number` | Dot-prefix float `.5` | `lexer.rs` line ~251 |
| `parse error: expected property value, got Dot` | Dot-prefix float `.15` in const | `lexer.rs` line ~251 |
| `UNHANDLED_COND(BinOp{...})` in SMT | Missing match arm in `cond_expr_to_smt` | `statechart.rs` line ~1024 |
| Rust says COUNTEREXAMPLE but Go says CORRECT | Run-block conditional not gated | `encode.rs` ITE encoding |
| Rust says COUNTEREXAMPLE on no-assertion spec | No assertion guard in check mode | `main.rs` `run_check_mode` |
| Declaration order differs from Go | Emission order in encoder | `encode.rs` / `statechart.rs` declaration emission |
| Block numbering differs | Counter scheme for ITE booleans | `encode.rs` block-ID generation |
| "nothing to run" on const-only spec | `encode_program` early return | `encode.rs` top-level |
