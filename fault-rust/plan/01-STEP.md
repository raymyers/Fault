# Definition of Done — Any Task

A task from `01-PLAN.md` is **done** when ALL of the following hold.

---

## 1. Tested

- [ ] All data-driven tests pass (`cargo test`).
- [ ] New behavior has at least one test case backed by a flat fixture file in `testdata/`.
- [ ] If the task touches execution or SMT output, the oracle script (`oracle.sh`) has been run and the expected output committed.
- [ ] Edge cases identified during implementation have test coverage.

## 2. Committed

- [ ] Code is committed to the working branch with a clear, single-purpose commit message.
- [ ] No untracked or unstaged changes related to the task remain.
- [ ] The commit compiles cleanly (`cargo build`), passes `cargo clippy` with no warnings, and is formatted (`cargo fmt`).

## 3. Design-Reviewed for Simplicity & Testability

- [ ] No unnecessary abstractions, traits, or generics. Would a new contributor understand this in 5 minutes?
- [ ] Public API surface is minimal — only expose what other modules need.
- [ ] State is explicit (passed as arguments or in clear structs), not hidden in globals or thread-locals.
- [ ] Functions are small enough to test in isolation. If a function is >40 lines, consider splitting.
- [ ] Types mirror the Lean semantics definitions. Deviations are documented with rationale.

## 4. Plan Updated

- [ ] The corresponding checkbox in `01-PLAN.md` is ticked (`[x]`).
- [ ] If the task turned out differently than planned (scope change, unexpected dependency), update the plan text to reflect reality.

## 5. Complex Tasks → Progress Doc

If a task is non-trivial (estimated >2 hours, involves multiple sub-steps, or has open questions):

- [ ] Create `fault-rust/plan/01-progress/<milestone>-<task-slug>.md`.
- [ ] Track sub-steps, blockers, and decisions in that file.
- [ ] Link to it from `01-PLAN.md` next to the task bullet.
- [ ] Mark the progress doc as complete when the parent task is done.

Template for a progress doc:

```markdown
# M<N>: <Task Title>

## Status: in-progress | done

## Sub-steps
- [ ] ...
- [ ] ...

## Decisions
- <date>: Chose X over Y because ...

## Blockers
- (none)
```

---

## Quick Checklist (copy into PR or commit message)

```
- [ ] Tests pass
- [ ] Oracle fixtures up to date (if applicable)
- [ ] Committed, compiles, clippy clean, formatted
- [ ] Reviewed for simplicity
- [ ] Plan checkbox ticked
- [ ] Progress doc created (if complex)
```
