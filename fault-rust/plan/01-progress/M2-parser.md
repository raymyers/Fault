# M2: Parser

## Status: done

## Decisions
- Hand-written recursive-descent parser (no parser generator dependency)
- Parser lives in `fault_syntax` crate as `parser` module (produces AST types from same crate)
- Lexer is a separate `lexer` module within `fault_syntax`

## Sub-steps
- [x] Lexer: tokenize all keywords, operators, punctuation, literals, identifiers
- [x] Parser: spec-level (spec decl, def, stock, flow, for/init/run)
- [x] Parser: expressions (arithmetic, comparison, logical, choose, history, prefix)
- [x] Parser: statements (assignment, flow assign, if/else, call, parallel)
- [x] Parser: invariants (assert, assume, when/then, temporal)
- [x] Parser: system files (system decl, import, component, global, start)
- [x] Data tests: parse all fixtures, verify no parse errors
