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

257 tests across all crates. The test suite includes:

- **Unit tests**: lexer, parser, evaluator, SSA versioning, temporal checker
- **Fixture tests**: parse → resolve → encode for 18+ standard specs, 8 external
  examples, 3 swap specs, 6 conditional specs, and 8 statechart specs
- **Integration tests**: full CLI pipeline (smt, parse, check modes), badspec
  validation, import loading (including circular imports)
- **Error path tests**: lexer errors, parser errors, missing files, invalid inputs

```sh
# Run all tests
cargo test

# Clippy (zero warnings enforced via workspace lints)
cargo clippy --all-targets -- -D warnings

# Coverage (requires cargo-llvm-cov + llvm-tools-preview)
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov
cargo llvm-cov --summary-only

# Mutation testing (requires cargo-mutants)
cargo install cargo-mutants
cargo mutants --file fault_smt/src/ssa.rs --timeout 30
```

## Architecture

The compiler pipeline is:

```
.fspec/.fsystem source
  → fault_syntax (lex + parse → AST)
  → fault_resolve (name resolution + validation)
  → fault_smt (SSA encoding → SMT-LIB2)
  → Z3 solver (check-sat / get-model)
  → fault_cli (format counterexample output)
```

### Crate Dependency Graph

```
fault_syntax
  ↓
fault_eval (expression evaluator, uses AST types)
  ↓
fault_resolve (name resolution, import loading)
  ↓         ↘
fault_exec    fault_smt (SSA encoding → SMT-LIB2)
  ↓                 ↓
fault_temporal    fault_cli (CLI + Z3 integration)
```

### Key Design Decisions

- **SSA versioning** (`fault_smt/src/ssa.rs`): Every variable gets monotonically
  increasing version suffixes (`x_0`, `x_1`, …) for bounded unrolling. Supports
  snapshot/restore for branching and merge-max for join points.
- **Statechart encoding** (`fault_smt/src/statechart.rs`): State machines use Bool
  variables with ITE guards and advance/stay/choose transitions. Component states
  are tracked per-round with exclusive-or constraints.
- **Mixed-system encoding** (`fault_smt/src/encode.rs`): Handles specs that combine
  flow functions with statechart components, including target swaps and property
  overrides in init blocks.
- **Event log** (`fault_smt/src/event_log.rs`): Records encoding events
  (round starts, function entries/exits, variable updates) for structured
  counterexample output that matches the Go implementation's Logger.Print() format.
- **Temporal properties**: Assertions are negated for counterexample search
  (`assert always P` → `(or (not P_0) ... (not P_N))`). Assumptions are encoded
  directly. Supports `always`, `eventually`, `eventually-always`, `nmt`, `nft`.

### File Layout

```
fault-rust/
├── Cargo.toml              # Workspace root with clippy lints
├── fault_syntax/src/
│   ├── lexer.rs            # Tokenizer (keywords, operators, literals)
│   ├── parser.rs           # Recursive descent parser → AST
│   └── lib.rs              # AST types (Spec, System, Stmt, Expr, etc.)
├── fault_resolve/src/
│   ├── lib.rs              # Name resolution, alias expansion, dot flattening
│   ├── loader.rs           # Import loading with circular-import detection
│   └── validate.rs         # Pre-encode validation (missing run, empty funcs)
├── fault_eval/src/lib.rs   # Expression evaluator, FaultState, SVal
├── fault_exec/src/lib.rs   # Multi-round execution engine
├── fault_temporal/src/lib.rs # Temporal property checking
├── fault_smt/src/
│   ├── encode.rs           # Main SMT encoder (2900+ lines)
│   ├── statechart.rs       # Statechart → SMT encoding
│   ├── ssa.rs              # SSA version tracking
│   └── event_log.rs        # Encoding event log for output formatting
├── fault_cli/src/
│   ├── lib.rs              # Library entry point (run_check, run_smt, run_parse)
│   ├── main.rs             # CLI argument handling
│   └── z3_parse.rs         # Z3 model output parser and formatter
├── testdata/               # Fixture specs and oracle .smt2 files
└── plan/                   # Development planning documents
```

## Supported Fault Features

| Feature | Status | Notes |
|---------|--------|-------|
| Stocks & flows | ✅ | Inflow (`<-`), outflow (`->`), assign (`=`) |
| Functions | ✅ | `func{}` blocks with if/else, parallel (`\|`) |
| Imports | ✅ | Single, renamed, circular (with stub) |
| Constants | ✅ | Numeric, boolean, string (as Bool propositions) |
| Assertions | ✅ | `assert`, `assume`, `when...then` |
| Temporal | ✅ | `always`, `eventually`, `eventually-always`, `nmt`, `nft` |
| Statecharts | ✅ | `component`, `advance`, `stay`, `choose`, `leave` |
| Mixed systems | ✅ | Flows + statecharts in same spec |
| Target swaps | ✅ | `flow_inst.stock_ref = other_inst` in init |
| Property overrides | ✅ | `inst.prop = val` in init |
| History references | ✅ | `var[now-1]`, `var[0]` (fixed index) |
| Unknown variables | ✅ | `unknown` type (unconstrained Real) |

## License

See the repository root [LICENSE](../LICENSE) file.
