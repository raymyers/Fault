# Seed Instructions

> Verbatim capture of the original request that initiated this plan.

---

https://github.com/raymyers/Fault

Branch ray/rust-impl

Checkout that. Try out the rust cli, and make sure that Marrianne will find it works just as well as the Go CLI.

Try the examples: https://github.com/Fault-lang/examples

Tell me what you find, what are the gaps?

---

In the rust plans folder make an 02 PLAN and STEP md (similar idea to the 01 ones) that will not only address these that diverge, but find all others that reasonably can be found. Record the instructions up to this point as the SEED.

Commit push then execute STEP

---

## Discovery Process

Built both CLIs (`go build -o fault-go .` and `cargo build --release` in `fault-rust/`), installed Z3, and ran every example from Fault-lang/examples through both. Also diffed all internal `testdata/` fixtures against Rust CLI SMT output.

### Example-by-Example Results (Fault-lang/examples)

| Example | Go CLI | Rust CLI | Status |
|---|---|---|---|
| `fibonacci.fspec` | Shows run trace | "COUNTEREXAMPLE FOUND" (false alarm, no asserts) | ❌ diverge |
| `sandwich.fspec` | "no failure case" | "CORRECT" | ✅ agree |
| `cache.fspec` | Detailed execution trace | "COUNTEREXAMPLE FOUND" (raw Z3 model) | ⚠️ both find issue, output differs |
| `cache_unkn.fspec` | Execution trace | Parse error (`.5` float + bare `const`) | ❌ parse fail |
| `orchestrator.fspec` | "no failure case" | "COUNTEREXAMPLE FOUND" | ❌ semantic bug |
| `battery.fspec` | Panics (no run block) | Parse error (`.15` float) | ❌ parse fail |
| `position.fspec` | Panics (no run block) | Clean error | ✅ Rust better |
| `drone.fsystem` | Panics | UNHANDLED_COND error | ❌ both broken |
| `repl.fsystem` | "no failure case" | "COUNTEREXAMPLE FOUND" | ❌ diverge |

### Internal Testdata Fixture Diffs (Rust output vs expected.smt2)

- ✅ Match: asserts, bathtub2, indexes, strings, unknowns
- ❌ Cosmetic diffs (block numbering, declaration order): bathtub, booleans, history1-4, increment, simple, simpleA, all 8 statecharts
- ❌ strings2: Rust errors "nothing to run" on spec-only file with const expressions
- ❌ All conditionals (condwelse, multicond-5): Expected files are Go-generated single-line blobs; Rust output is multi-line. Block naming also differs.

### Root Causes Identified

1. **Lexer**: `.15` dot-prefix floats not recognized
2. **Parser**: bare `const name;` (no value) silently dropped
3. **SMT encoder**: `cond_expr_to_smt` missing `BinOp::Eq/Lt/Gt/Le/Ge` → `UNHANDLED_COND`
4. **SMT encoder**: Run-block conditionals (`if ... { ... }`) not gated properly — side-effects execute unconditionally
5. **SMT encoder**: Block numbering scheme differs from Go oracle (separate vs shared true/false counters)
6. **CLI**: No-assertion specs produce false "COUNTEREXAMPLE FOUND" (Z3 trivially sat)
7. **CLI**: Missing result formatter (raw Z3 model vs Go's execution trace)
8. **CLI**: Missing modes/flags: `-m ir`, `-m model`/`-m ast` naming, `-complete`, `-i`, `-output`
9. **CLI**: No TUI mode, no SOLVERCMD validation
10. **SMT encoder**: `strings2` spec-only files with const expressions not encoded
