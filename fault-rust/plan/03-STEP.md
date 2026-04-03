# How To Make Progress — Phase 3

You are improving the test quality, coverage, and code hygiene of the Fault Rust compiler.
This file is everything you need to pick up the next task and finish it correctly.

**Current state (2026-04-03):** 167 tests pass. All 7 external examples correct.
84.8% line coverage. Clippy: ~28 warnings (0 errors).

---

## 1. Orient Yourself

### What this phase is about

Phase 1 built the compiler. Phase 2 closed every correctness gap vs the Go CLI.
Phase 3 hardens the codebase: Clippy clean, coverage gaps filled, mutations killed,
production panics eliminated, large files split.

### Key Paths

| Path | What |
|------|------|
| `fault-rust/plan/03-PLAN.md` | Master plan — milestones and checkboxes |
| `fault-rust/plan/03-STEP.md` | This file — self-contained instructions |
| `fault-rust/fault_smt/src/encode.rs` | Largest file (2943 lines). Split target. |
| `fault-rust/fault_smt/src/ssa.rs` | SSA versioning — 48% mutation score, needs tests |
| `fault-rust/fault_smt/src/statechart.rs` | Statechart encoder — production unwraps |
| `fault-rust/fault_resolve/src/validate.rs` | Validation — 57% mutation score |
| `fault-rust/fault_cli/src/main.rs` | CLI entry point — 0% coverage |

### Build & Test Commands

```sh
cd fault-rust/fault-rust

# Build & test
source "$HOME/.cargo/env"       # If cargo not on PATH after restart
cargo build --release
cargo test                      # 167 tests

# Clippy (target: zero warnings)
cargo clippy --all-targets -- -D warnings

# Coverage (requires cargo-llvm-cov + llvm-tools-preview)
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov    # if not installed
cargo llvm-cov --json 2>&1 | python3 -c "
import json, sys
data = json.load(open('/dev/stdin'))
for d in data.get('data', []):
    for f in d.get('files', []):
        fn = f['filename'].rsplit('/', 1)[-1]
        l = f['summary']['lines']
        print(f'{fn}: {l[\"covered\"]}/{l[\"count\"]} ({l[\"percent\"]:.1f}%)')
    t = d['totals']['lines']
    print(f'TOTAL: {t[\"covered\"]}/{t[\"count\"]} ({t[\"percent\"]:.1f}%)')
"

# Mutation testing (requires cargo-mutants)
cargo install cargo-mutants     # if not installed
cargo mutants --file fault_smt/src/ssa.rs --timeout 30
cargo mutants --file fault_resolve/src/validate.rs --timeout 30
```

---

## 2. Pick a Task

Open `03-PLAN.md` and find the **first unchecked task** in milestone order.
Milestones should be tackled roughly in order: M31 → M32 → M33 → M34.
M35 and M36 are stretch goals.

---

## 3. Execute the Task

### M31 — Clippy Clean + Dead Code

**31a. Remove dead code:**
```sh
# Delete these two functions from encode.rs (they are dead):
grep -n "fn collect_modified_vars\b\|fn collect_modified_in_stmt\b" fault_smt/src/encode.rs
# Remove the function bodies. Then:
cargo test && cargo clippy --all-targets
```

**31b–31d. Auto-fixable warnings:**
```sh
# Let clippy fix what it can, then review:
cargo clippy --fix --allow-dirty --all-targets
cargo test  # Verify no regressions
# Manual review: collapsed ifs may need formatting cleanup.
```

**31e. Too-many-arguments fix:**
Introduce a struct for `encode_mixed_if_in_state` parameters:
```rust
struct MixedIfContext<'a> {
    cond: &'a Expr,
    then_branch: &'a [Stmt],
    else_branch: Option<&'a [Stmt]>,
    comp_name: &'a str,
    state_name: &'a str,
    spec_name: &'a str,
    // ...
}
```

**31f. Workspace lints:**
Add to root `Cargo.toml`:
```toml
[workspace.lints.clippy]
correctness = "deny"
suspicious = "warn"
perf = "warn"
style = "warn"
```
And in each crate's `Cargo.toml`:
```toml
[lints]
workspace = true
```

### M32 — Production Error Handling

**32a. Replace unwrap chains in statechart.rs:**
Find: `name.strip_prefix("__advance_").unwrap()` at lines ~918, 953, 976, 1015.
Replace with:
```rust
let target = name.strip_prefix("__advance_")
    .and_then(|s| s.strip_suffix("__"))
    .unwrap_or_else(|| name.strip_prefix("__advance_").unwrap_or(name));
```
Or better: extract a helper `fn parse_advance_target(name: &str) -> &str`.

**32b–32c. Replace panic! with debug_assert! or return:**
- `resolve/lib.rs:592`: Change `_ => panic!("expected FlowAssign")` to
  `_ => continue` or `debug_assert!(false, ...)`.
- `statechart.rs:1086`: Return a placeholder string with an error comment in the SMT.

### M33 — Coverage Gaps

**33a. CLI testability — extract library function:**
In `fault_cli/src/main.rs`, extract the core pipeline to `fault_cli/src/lib.rs`:
```rust
pub enum Mode { Smt, Parse, Check }

pub struct Output {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: i32,
}

pub fn run(mode: Mode, file_path: &str) -> Output {
    // Move logic from main() here
    // Replace process::exit with setting exit_code
}
```
Then in `fault_cli/src/main.rs`:
```rust
fn main() {
    let output = fault_cli::run(mode, file_path);
    print!("{}", output.stdout);
    eprint!("{}", output.stderr);
    std::process::exit(output.exit_code);
}
```
Add tests in `fault_cli/src/lib.rs`:
```rust
#[cfg(test)]
mod tests {
    #[test]
    fn smt_mode_simple_spec() { ... }
    #[test]
    fn check_mode_counterexample() { ... }
    // etc.
}
```

**33b. Parser coverage — add error-path fixtures:**
Create `testdata/parse_errors/` with `.fspec` files that exercise parser error paths:
- `empty.fspec` — empty file
- `bad_import.fspec` — `import(42)` (non-string path)
- `missing_semi.fspec` — missing semicolons
- `unterminated_string.fspec` — `def foo = "hello`
Add tests that assert `parse_spec(src).is_err()`.

**33e. Encode coverage — target swap and const-bool fixtures:**
Create fixture test `.fspec` files that exercise:
- Target swap: `init { flow_inst.stock = other_inst }`
- Property override: `init { inst.prop = 5 }`
- Bool constant: `const flag = true;`
These hit the uncovered lines 119–133 and 274–275 in encode.rs.

### M34 — Mutation Hardening

**34a. SSA mutation kills:**
Add to `fault_smt/src/ssa.rs` tests module:
```rust
#[test]
fn snapshot_restore_roundtrip() {
    let mut ssa = Ssa::new();
    ssa.next_name("x");  // x_0
    ssa.next_name("x");  // x_1
    let snap = ssa.snapshot();
    ssa.next_name("x");  // x_2
    assert_eq!(ssa.current("x"), 2);
    ssa.restore(snap);
    assert_eq!(ssa.current("x"), 1);
}

#[test]
fn merge_max_takes_higher() {
    let mut ssa = Ssa::new();
    ssa.next_name("a");  // a_0
    ssa.next_name("a");  // a_1
    let snap = ssa.snapshot();  // {a: 1}
    ssa.restore(Ssa::new().snapshot());  // reset to empty
    ssa.merge_max(snap);
    assert_eq!(ssa.current("a"), 1);
}

#[test]
fn current_ro_does_not_bump() {
    let mut ssa = Ssa::new();
    let v = ssa.current_ro("x");
    assert_eq!(v, 0);
    // Should NOT have created a version
    assert!(!ssa.has("x"));
}

#[test]
fn has_after_bump() {
    let mut ssa = Ssa::new();
    assert!(!ssa.has("x"));
    ssa.next_name("x");
    assert!(ssa.has("x"));
}

#[test]
fn set_version_overrides() {
    let mut ssa = Ssa::new();
    ssa.set_version("y", 5);
    assert_eq!(ssa.current("y"), 5);
}
```

**34b. Validate.rs mutation kills:**
Add to `fault_resolve/tests/badspec_fixtures.rs` (or create new test file):
- A spec with `flows` but no run block → should trigger MissingRunBlock
- A spec with `stocks` but no run block → should trigger MissingRunBlock
- A spec with neither flows nor stocks and no invariants → should trigger MissingRunBlock
- A spec with only constants and no run block → should NOT trigger MissingRunBlock

**Run after each change:**
```sh
cargo test
cargo mutants --file <path> --timeout 30
```

---

## 4. Verify

After completing any task:

```sh
# All tests pass
cargo test

# Clippy clean (after M31)
cargo clippy --all-targets -- -D warnings

# Coverage improved (after M33)
cargo llvm-cov --summary-only --json 2>&1 | python3 -c "..."  # see above

# Mutation score improved (after M34)
cargo mutants --file <modified_file> --timeout 30
```

---

## 5. Update the Plan

Edit `03-PLAN.md`:
- Check off the completed task: `- [ ]` → `- [x]`
- Add commit hash
- Update baseline metrics if they changed

---

## 6. Commit

```sh
git add -A
git commit -m "M3Xx: <description>

<details>

Co-authored-by: openhands <openhands@all-hands.dev>"
```

Use the milestone tag (e.g., `M31a`, `M33a`) as prefix.

---

## Quick Reference: What to Tackle First

| Priority | Task | Impact | Effort |
|----------|------|--------|--------|
| 1 | **M31a** Dead code removal | Clippy clean | 5 min |
| 2 | **M31b-d** Auto-fix clippy | Clippy clean | 10 min |
| 3 | **M34a** SSA mutation tests | Catches real bugs | 20 min |
| 4 | **M32a** Unwrap elimination | No production panics | 15 min |
| 5 | **M33a** CLI testability | 0% → 60% coverage | 30 min |
| 6 | **M34b** Validate mutation tests | Catches validation bugs | 20 min |
| 7 | **M33e** Encode coverage fixtures | Covers target swap/const | 20 min |
| 8 | **M31f** Workspace lints | Prevents regressions | 10 min |
| 9 | **M36a-c** encode.rs split | Maintainability | 45 min |
