# How To Make Progress on fault-rust

You are implementing a Rust compiler for the Fault bounded model-checking language.
This file is everything you need to pick up the next task and finish it correctly.

---

## 1. Orient Yourself

### Project

Fault compiles `.fspec`/`.fsystem` models into SMT-LIB2, then asks Z3 for counterexamples to assertions. You are reimplementing it in Rust.

### Key Paths (all relative to repo root)

| Path | What |
|------|------|
| `fault-rust/` | Your Rust workspace (create with `cargo init` if it doesn't exist yet) |
| `fault-rust/plan/01-PLAN.md` | Master plan — milestones and task checkboxes |
| `fault-rust/plan/01-progress/` | Per-task progress docs (only for complex tasks) |
| `fault-rust/testdata/` | Data-driven test fixtures |
| `semantics/FaultSemantics/` | **Lean 4 formalization — source of truth for semantics** |
| `semantics/docs/implementation.md` | Language-agnostic implementation guide derived from Lean |
| `grammar/FaultLexer.g4`, `grammar/FaultParser.g4` | ANTLR4 grammar (concrete syntax) |
| `generator/testdata/` | Existing `.fspec` + `.smt2` pairs from Go compiler |
| repo root `go.mod`, `main.go` | Go reference compiler — the oracle |

### Build the Go Oracle (once)

```sh
cd <repo-root> && go build -o fault_bin .
# Generate expected SMT:  ./fault_bin -m smt -f some.fspec
# Run with solver:        SOLVERCMD=z3 SOLVERARG="-in" ./fault_bin -f some.fspec
```

---

## 2. Pick the Next Task

1. Open `fault-rust/plan/01-PLAN.md`.
2. Find the **earliest milestone with an unchecked `[ ]` bullet**.
3. Within that milestone, pick the **first unchecked bullet** (task order is dependency order).
4. That is your task. Do only that task.

---

## 3. Work Loop

```
READ    → Read the task bullet. Read the Lean file(s) it references.
         Read the corresponding Go code if the Lean reference is unclear.
         Read any existing Rust code in the module you'll be changing.

DESIGN  → Decide on types and function signatures BEFORE writing bodies.
         Keep them as close to the Lean definitions as possible.
         If the task is complex, create a progress doc (see §6).

TEST    → Write or update a data-driven test FIRST.
         Test fixture = flat file in fault-rust/testdata/.
         If the task involves execution or SMT output, generate expected
         output from the Go oracle and commit it.

BUILD   → Implement the minimum code to pass the test.
         cargo build && cargo test && cargo clippy && cargo fmt

REVIEW  → Re-read your diff. Check against the Definition of Done (§5).

COMMIT  → Single-purpose commit. Message format:
           M<n>: <short description>
           e.g. "M1: Define Val and operator enums"

UPDATE  → Tick the checkbox in 01-PLAN.md. Commit that too (same or next commit).
         If the task scope changed, update the plan text.
```

---

## 4. Test Conventions

### Fixture layout

```
fault-rust/testdata/<name>/
  input.fspec            # or input.fsystem
  expected.smt2          # Go oracle: fault_bin -m smt -f input.fspec
  expected.result.json   # (optional) counterexample
  oracle.sh              # idempotent script to regenerate expected.* from Go
```

### Rules

- Every new behavior gets at least one fixture-backed test.
- Tests read input, run Rust pipeline, diff against `expected.*`.
- Do NOT hand-roll assertions that duplicate the logic under test. Compare against oracle output or hand-checked snapshots.
- If Go oracle output doesn't exist yet for a fixture, generate it and commit it before writing Rust code.

---

## 5. Definition of Done

A task is **done** when ALL of the following hold:

### Tested
- All data-driven tests pass (`cargo test`).
- New behavior has at least one test backed by a fixture file.
- Oracle fixtures are up to date (if applicable).
- Edge cases identified during implementation have coverage.

### Committed
- Code is on the working branch with a clear commit message.
- Compiles cleanly, `cargo clippy` warns on nothing, `cargo fmt` is clean.

### Design-Reviewed for Simplicity
- No unnecessary abstractions, traits, or generics. A new reader understands it in 5 minutes.
- Public API surface is minimal.
- State is explicit (arguments and structs), not global or hidden.
- Functions ≤ ~40 lines. Split if bigger.
- Types mirror Lean semantics. Deviations are commented with rationale.

### Plan Updated
- Checkbox in `01-PLAN.md` ticked `[x]`.
- Plan text updated if scope changed.

---

## 6. Complex Tasks → Progress Doc

If a task has multiple sub-steps, open questions, or will take more than ~2 hours:

1. Create `fault-rust/plan/01-progress/M<n>-<slug>.md`.
2. Track sub-steps, decisions, and blockers there.
3. Link to it from the task bullet in `01-PLAN.md`.
4. Mark it done when the parent task is done.

Template:

```markdown
# M<n>: <Task Title>

## Status: in-progress | done

## Sub-steps
- [ ] ...

## Decisions
- <date>: Chose X over Y because ...

## Blockers
- (none)
```

---

## 7. Reference Lookup Cheat-Sheet

When implementing a task, consult these in order:

1. **Lean file** named in the task bullet (e.g. `Syntax.lean` → `semantics/FaultSemantics/Syntax.lean`).
   This is the formal definition. Match it.
2. **`semantics/docs/implementation.md`** — prose explanation of each Lean construct with pseudocode.
3. **Go source** in the repo root (e.g. `ast/ast.go`, `llvm/compiler.go`, `generator/`).
   Use to understand practical behavior, edge cases, and to generate oracle output.
4. **ANTLR grammar** (`grammar/FaultParser.g4`) — for parser tasks.
5. **Existing test fixtures** (`generator/testdata/`) — concrete examples of inputs and expected outputs.
