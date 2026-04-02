# M3: Name Resolution

## Status: done

## Decisions
- `fault_resolve` crate: one lib.rs file (split if > 300 lines)
- AliasMap = HashMap<String, String> (simple, no trait indirection)
- resolve functions consume and return owned AST nodes (no mutation)
- ResolvedProgram mirrors Lean definition exactly

## Sub-steps
- [x] flatten_name, AliasMap, resolve_alias (with cycle limit)
- [x] resolve_expr: Dot → Var(flat), recursively walk all variants
- [x] resolve_stmt, resolve_invariant: walk full AST
- [x] Import merging: merge stocks/flows/constants/invariants
- [x] Component validation: validInStateFunc
- [x] ResolvedProgram struct + Spec::resolve + System::resolve
- [x] Data tests: parse fixtures → resolve → verify no Dot nodes remain
