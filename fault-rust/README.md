# fault-rust

Rust implementation of the [Fault](https://github.com/raymyers/Fault) bounded model-checking compiler. Fault is a modeling language for building system dynamic models and checking them using a combination of first-order logic and probability.

This implementation produces the same SMT-LIB2 output as the reference Go compiler for all supported spec features: stocks, flows, statecharts, imports, assertions, temporal properties, and `unknown` variables.

## Workspace Crates

| Crate | Purpose |
|-------|---------|
| `fault_syntax` | Lexer, parser, and AST types (`.fspec` / `.fsystem`) |
| `fault_resolve` | Name resolution, import loading, validation |
| `fault_eval` | Expression evaluator and execution state |
| `fault_exec` | Multi-round parallel executor |
| `fault_temporal` | Temporal property checker (always, eventually, etc.) |
| `fault_smt` | SMT-LIB2 encoder (SSA versioning, statecharts, invariants) |
| `fault_cli` | Command-line interface and library entry point |

## Quick Start

```sh
# Build
cargo build --release

# Run (SMT mode — emit SMT-LIB2 to stdout)
cargo run --release -- -m smt -f input.fspec

# Run (check mode — requires Z3 solver)
export SOLVERCMD="z3"
export SOLVERARG="-in"
cargo run --release -- -f input.fspec

# Check mode with raw Z3 model output
cargo run --release -- -m check --raw -f input.fspec

# Parse mode (debug AST dump)
cargo run --release -- -m parse -f input.fspec
```

### Example Output

When a counterexample is found, the output shows a round-by-round trace
matching the Go implementation's format:

```
$ fault-rust -f testdata/asserts/input.fspec

Start model, run for 4 rounds
-----------------------------------
   Run function asserts_test_fn (round 1)
      Set variable asserts_test_target_value to value 20.0
   Run function asserts_test_fn (round 2)
      asserts_test_target_value: 20.0 → 10.0
   Run function asserts_test_fn (round 3)
      asserts_test_target_value: 10.0 → 5.0
   Run function asserts_test_fn (round 4)
      asserts_test_target_value: 5.0 → 2.5
```

When no assertion is violated:
```
$ fault-rust -f testdata/examples/orchestrator/orchestrator.fspec
Fault could not find a failure case. All good!
```

## Testing

```sh
# Run all tests
cargo test

# Clippy (zero warnings enforced)
cargo clippy --all-targets -- -D warnings
```

## Architecture

The compiler pipeline is:

```
.fspec/.fsystem source
  → fault_syntax (lex + parse → AST)
  → fault_resolve (name resolution + validation)
  → fault_smt (SSA encoding → SMT-LIB2)
  → Z3 solver (check-sat / get-model)
```

Key design decisions:
- **SSA versioning** (`fault_smt/src/ssa.rs`): Every variable gets monotonically increasing version suffixes (`x_0`, `x_1`, …) for bounded unrolling.
- **Statechart encoding** (`fault_smt/src/statechart.rs`): State machines use Bool variables with ITE guards and advance/stay transitions.
- **Mixed-system encoding** (`fault_smt/src/encode.rs`): Handles specs that combine flow functions with statechart components.

## License

See the repository root [LICENSE](../LICENSE) file.
