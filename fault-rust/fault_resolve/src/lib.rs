//! Name resolution for the Fault language.
//!
//! Mirrors `semantics/FaultSemantics/Resolve.lean`:
//! - Flatten dotted names to underscore-delimited strings
//! - Resolve aliases (stock swaps) with cycle limit
//! - Walk AST replacing `Expr::Dot` with `Expr::Var(flat_name)`
//! - Merge imports, validate components
//! - Build `ResolvedProgram` for execution

pub mod loader;
pub mod validate;

use std::collections::HashMap;

use fault_syntax::*;

// ── Name flattening (Resolve.lean:21) ───────────────────────────────

/// Join name parts with underscore separators.
/// Matches Go's `IdString()`: `strings.Join(rawid, "_")`.
pub fn flatten_name(parts: &[&str]) -> String {
    parts.join("_")
}

// ── Alias resolution (Resolve.lean:49) ──────────────────────────────

/// Map from flat names to flat names, created by stock swaps.
pub type AliasMap = HashMap<String, String>;

/// Recursively resolve an alias, with fuel to prevent infinite loops.
/// Matches Go's `AliasToBaseRaw`.
pub fn resolve_alias(aliases: &AliasMap, name: &str, fuel: usize) -> String {
    if fuel == 0 {
        return name.to_string();
    }
    match aliases.get(name) {
        Some(resolved) => resolve_alias(aliases, resolved, fuel - 1),
        None => name.to_string(),
    }
}

const ALIAS_FUEL: usize = 100;

// ── Expression resolution (Resolve.lean:68) ─────────────────────────

/// Resolve all Dot nodes in an expression to flat Var nodes.
/// `scope` is the current context path (e.g. `["specname", "flowname"]`).
pub fn resolve_expr(aliases: &AliasMap, scope: &[String], expr: Expr) -> Expr {
    match expr {
        Expr::Dot { expr: base, field } => {
            let resolved_base = resolve_expr(aliases, scope, *base);
            match resolved_base {
                Expr::Var(x) => {
                    let flat = format!("{}_{}", x, field);
                    Expr::Var(resolve_alias(aliases, &flat, ALIAS_FUEL))
                }
                _ => {
                    let mut parts: Vec<&str> = scope.iter().map(|s| s.as_str()).collect();
                    parts.push(&field);
                    let flat = flatten_name(&parts);
                    Expr::Var(resolve_alias(aliases, &flat, ALIAS_FUEL))
                }
            }
        }
        Expr::Var(x) => Expr::Var(resolve_alias(aliases, &x, ALIAS_FUEL)),
        Expr::BinOp { op, left, right } => Expr::BinOp {
            op,
            left: Box::new(resolve_expr(aliases, scope, *left)),
            right: Box::new(resolve_expr(aliases, scope, *right)),
        },
        Expr::UnOp { op, expr: inner } => Expr::UnOp {
            op,
            expr: Box::new(resolve_expr(aliases, scope, *inner)),
        },
        Expr::History { name, offset } => Expr::History {
            name: resolve_alias(aliases, &name, ALIAS_FUEL),
            offset,
        },
        Expr::Index { name, index } => Expr::Index {
            name: resolve_alias(aliases, &name, ALIAS_FUEL),
            index,
        },
        Expr::Choose(es) => Expr::Choose(
            es.into_iter()
                .map(|e| resolve_expr(aliases, scope, e))
                .collect(),
        ),
        lit @ Expr::Lit(_) => lit,
    }
}

// ── Statement resolution (Resolve.lean:83) ──────────────────────────

/// Resolve all expressions in a statement.
pub fn resolve_stmt(aliases: &AliasMap, scope: &[String], stmt: Stmt) -> Stmt {
    match stmt {
        Stmt::FlowAssign { name, op, expr } => Stmt::FlowAssign {
            name: resolve_alias(aliases, &name, ALIAS_FUEL),
            op,
            expr: resolve_expr(aliases, scope, expr),
        },
        Stmt::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => Stmt::IfThenElse {
            cond: resolve_expr(aliases, scope, cond),
            then_branch: then_branch
                .into_iter()
                .map(|s| resolve_stmt(aliases, scope, s))
                .collect(),
            else_branch: else_branch
                .into_iter()
                .map(|s| resolve_stmt(aliases, scope, s))
                .collect(),
        },
        Stmt::Call(n) => Stmt::Call(n),
        Stmt::Advance(n) => Stmt::Advance(n),
        Stmt::Stay => Stmt::Stay,
        Stmt::Seq(ss) => Stmt::Seq(
            ss.into_iter()
                .map(|s| resolve_stmt(aliases, scope, s))
                .collect(),
        ),
        Stmt::Parallel(ss) => Stmt::Parallel(
            ss.into_iter()
                .map(|s| resolve_stmt(aliases, scope, s))
                .collect(),
        ),
    }
}

/// Resolve all expressions in an invariant.
pub fn resolve_invariant(aliases: &AliasMap, scope: &[String], inv: Invariant) -> Invariant {
    match inv {
        Invariant::Assert { expr, temporal } => Invariant::Assert {
            expr: resolve_expr(aliases, scope, expr),
            temporal,
        },
        Invariant::Assume { expr, temporal } => Invariant::Assume {
            expr: resolve_expr(aliases, scope, expr),
            temporal,
        },
        Invariant::AssertWhen {
            guard,
            body,
            temporal,
        } => Invariant::AssertWhen {
            guard: resolve_expr(aliases, scope, guard),
            body: resolve_expr(aliases, scope, body),
            temporal,
        },
        Invariant::AssumeWhen {
            guard,
            body,
            temporal,
        } => Invariant::AssumeWhen {
            guard: resolve_expr(aliases, scope, guard),
            body: resolve_expr(aliases, scope, body),
            temporal,
        },
    }
}

// ── Import resolution (Resolve.lean:108) ────────────────────────────

/// Merge stock definitions from multiple specs.
pub fn merge_stocks(specs: &[Spec]) -> Vec<StockDef> {
    specs.iter().flat_map(|s| s.stocks.clone()).collect()
}

/// Merge flow definitions from multiple specs.
pub fn merge_flows(specs: &[Spec]) -> Vec<FlowDef> {
    specs.iter().flat_map(|s| s.flows.clone()).collect()
}

/// Merge constant definitions from multiple specs.
pub fn merge_constants(specs: &[Spec]) -> Vec<ConstDef> {
    specs.iter().flat_map(|s| s.constants.clone()).collect()
}

/// Merge invariants from multiple specs.
pub fn merge_invariants(specs: &[Spec]) -> Vec<Invariant> {
    specs.iter().flat_map(|s| s.invariants.clone()).collect()
}

// ── Component validation (Resolve.lean:134) ─────────────────────────

/// Check whether a statement is valid inside a component state function.
/// State functions may only call advance/stay/call and use if/then/else.
/// FlowAssign is NOT allowed.
pub fn valid_in_state_func(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Advance(_) | Stmt::Stay | Stmt::Call(_) => true,
        Stmt::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            then_branch.iter().all(valid_in_state_func)
                && else_branch.iter().all(valid_in_state_func)
        }
        Stmt::Seq(ss) | Stmt::Parallel(ss) => ss.iter().all(valid_in_state_func),
        Stmt::FlowAssign { .. } => false,
    }
}

/// Check that a component definition is well-formed.
pub fn comp_well_formed(comp: &CompDef) -> bool {
    comp.states
        .iter()
        .all(|(_, body)| body.iter().all(valid_in_state_func))
}

// ── ResolvedProgram (Resolve.lean:158) ──────────────────────────────

/// A fully resolved program ready for execution.
/// All names are flattened, aliases resolved, imports merged.
#[derive(Debug, Clone)]
pub struct ResolvedProgram {
    pub stocks: Vec<StockDef>,
    pub flows: Vec<FlowDef>,
    pub constants: Vec<ConstDef>,
    pub components: Vec<CompDef>,
    pub invariants: Vec<Invariant>,
    pub start_states: Vec<(Name, Name)>,
    pub rounds: u64,
    pub init_block: Vec<Stmt>,
    pub run_block: Vec<Stmt>,
    pub var_names: Vec<Name>,
    /// Constants from imported specs: (imported_spec_name, constants).
    /// These get declared with the imported spec's name prefix, not the
    /// importing spec's prefix.
    pub imported_constants: Vec<(Name, Vec<ConstDef>)>,
    /// Mapping from import alias to imported spec name.
    /// Used by the encoder to resolve cross-spec references.
    pub import_alias_map: HashMap<Name, Name>,
}

/// Build a fully resolved program from a Spec (Resolve.lean:182).
/// Applies name resolution to all expressions in invariants,
/// init/run blocks, and flow function bodies.
pub fn resolve_spec(spec: Spec) -> ResolvedProgram {
    let aliases = AliasMap::new();
    let scope: Vec<String> = vec![];

    let (rounds, init_block, run_block) = match spec.run_block {
        Some((n, init, run)) => (n, init, run),
        None => (0, vec![], vec![]),
    };

    // Merge imported definitions (Resolve.lean §8.7)
    let mut all_stocks = spec.stocks;
    let mut all_flows: Vec<FlowDef> = spec.flows;
    let all_constants = spec.constants;
    let mut all_invariants = spec.invariants;

    for (idx, imported) in spec.imported_specs.iter().enumerate() {
        let alias = spec
            .import_decls
            .get(idx)
            .map(|d| d.alias.as_str())
            .unwrap_or(&imported.name);

        // Add imported stocks with alias prefix: alias.stock_name
        for stock in &imported.stocks {
            all_stocks.push(StockDef {
                name: format!("{}.{}", alias, stock.name),
                props: stock.props.clone(),
            });
        }
        // Add imported flows with alias prefix: alias.flow_name
        // Stock type references within these flows also get prefixed.
        for flow in &imported.flows {
            let prefixed_stocks: Vec<(Name, Name)> = flow
                .stocks
                .iter()
                .map(|(ref_name, type_name)| (ref_name.clone(), format!("{}.{}", alias, type_name)))
                .collect();
            all_flows.push(FlowDef {
                name: format!("{}.{}", alias, flow.name),
                stocks: prefixed_stocks,
                funcs: flow.funcs.clone(),
            });
        }
        // Add imported invariants
        all_invariants.extend(imported.invariants.clone());
    }

    // Collect imported constants separately (they keep their original spec prefix)
    let mut imported_constants: Vec<(Name, Vec<ConstDef>)> = Vec::new();
    let mut import_alias_map: HashMap<Name, Name> = HashMap::new();
    for (idx, imported) in spec.imported_specs.iter().enumerate() {
        let alias = spec
            .import_decls
            .get(idx)
            .map(|d| d.alias.clone())
            .unwrap_or_else(|| imported.name.clone());
        import_alias_map.insert(alias.clone(), imported.name.clone());
        if !imported.constants.is_empty() {
            imported_constants.push((imported.name.clone(), imported.constants.clone()));
        }
    }

    let var_names: Vec<Name> = all_stocks
        .iter()
        .flat_map(|st| st.props.iter().map(|(n, _)| n.clone()))
        .collect();

    let resolved_invariants = all_invariants
        .into_iter()
        .map(|inv| resolve_invariant(&aliases, &scope, inv))
        .collect();

    let resolved_init = init_block
        .into_iter()
        .map(|s| resolve_stmt(&aliases, &scope, s))
        .collect();

    let resolved_run = run_block
        .into_iter()
        .map(|s| resolve_stmt(&aliases, &scope, s))
        .collect();

    let resolved_flows = all_flows
        .into_iter()
        .map(|f| resolve_flow_def(&aliases, &scope, f))
        .collect();

    ResolvedProgram {
        stocks: all_stocks,
        flows: resolved_flows,
        constants: all_constants,
        components: vec![],
        invariants: resolved_invariants,
        start_states: vec![],
        rounds,
        init_block: resolved_init,
        run_block: resolved_run,
        var_names,
        imported_constants,
        import_alias_map,
    }
}

/// Build a fully resolved program from a System with imported Specs (Resolve.lean:195).
pub fn resolve_system(sys: System) -> ResolvedProgram {
    let aliases = AliasMap::new();
    let scope: Vec<String> = vec![];

    let (rounds, init_block, run_block) = match sys.run_block {
        Some((n, init, run)) => (n, init, run),
        None => (0, vec![], vec![]),
    };

    let stocks = merge_stocks(&sys.imports);
    let var_names: Vec<Name> = stocks
        .iter()
        .flat_map(|st| st.props.iter().map(|(n, _)| n.clone()))
        .collect();

    let mut all_invariants = sys.invariants;
    all_invariants.extend(merge_invariants(&sys.imports));

    let resolved_invariants = all_invariants
        .into_iter()
        .map(|inv| resolve_invariant(&aliases, &scope, inv))
        .collect();

    let resolved_init = init_block
        .into_iter()
        .map(|s| resolve_stmt(&aliases, &scope, s))
        .collect();

    let resolved_run = run_block
        .into_iter()
        .map(|s| resolve_stmt(&aliases, &scope, s))
        .collect();

    ResolvedProgram {
        stocks,
        flows: merge_flows(&sys.imports),
        constants: merge_constants(&sys.imports),
        components: sys.components,
        invariants: resolved_invariants,
        start_states: sys.start_states,
        rounds,
        init_block: resolved_init,
        run_block: resolved_run,
        var_names,
        imported_constants: vec![],
        import_alias_map: HashMap::new(),
    }
}

/// Resolve all expressions in flow function bodies.
fn resolve_flow_def(aliases: &AliasMap, scope: &[String], flow: FlowDef) -> FlowDef {
    FlowDef {
        name: flow.name,
        stocks: flow.stocks,
        funcs: flow
            .funcs
            .into_iter()
            .map(|(name, body)| {
                let resolved_body = body
                    .into_iter()
                    .map(|s| resolve_stmt(aliases, scope, s))
                    .collect();
                (name, resolved_body)
            })
            .collect(),
    }
}

// ── Helpers ─────────────────────────────────────────────────────────

/// Check whether an expression tree contains any `Expr::Dot` nodes.
/// After resolution, this should return false.
pub fn has_dots(expr: &Expr) -> bool {
    match expr {
        Expr::Dot { .. } => true,
        Expr::BinOp { left, right, .. } => has_dots(left) || has_dots(right),
        Expr::UnOp { expr, .. } => has_dots(expr),
        Expr::Choose(es) => es.iter().any(has_dots),
        Expr::Lit(_) | Expr::Var(_) | Expr::History { .. } | Expr::Index { .. } => false,
    }
}

/// Check whether a statement tree contains any `Expr::Dot` nodes.
pub fn stmt_has_dots(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::FlowAssign { expr, .. } => has_dots(expr),
        Stmt::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            has_dots(cond)
                || then_branch.iter().any(stmt_has_dots)
                || else_branch.iter().any(stmt_has_dots)
        }
        Stmt::Call(_) | Stmt::Advance(_) | Stmt::Stay => false,
        Stmt::Seq(ss) | Stmt::Parallel(ss) => ss.iter().any(stmt_has_dots),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flatten_name() {
        assert_eq!(
            flatten_name(&["myspec", "mybuffer", "f", "target", "value"]),
            "myspec_mybuffer_f_target_value"
        );
        assert_eq!(
            flatten_name(&["simple", "l", "vault", "value"]),
            "simple_l_vault_value"
        );
        assert_eq!(flatten_name(&["x"]), "x");
        assert_eq!(flatten_name(&[]), "");
    }

    #[test]
    fn test_resolve_alias_simple() {
        let mut aliases = AliasMap::new();
        aliases.insert("a".into(), "b".into());
        aliases.insert("b".into(), "c".into());

        assert_eq!(resolve_alias(&aliases, "a", 100), "c");
        assert_eq!(resolve_alias(&aliases, "b", 100), "c");
        assert_eq!(resolve_alias(&aliases, "c", 100), "c");
        assert_eq!(resolve_alias(&aliases, "unknown", 100), "unknown");
    }

    #[test]
    fn test_resolve_alias_fuel_limit() {
        let mut aliases = AliasMap::new();
        // Create cycle: a → b → a
        aliases.insert("a".into(), "b".into());
        aliases.insert("b".into(), "a".into());

        // With fuel, won't infinite loop — returns whatever name fuel runs out on
        let result = resolve_alias(&aliases, "a", 10);
        // After 10 steps: a→b→a→b→... last resolved is either "a" or "b"
        assert!(result == "a" || result == "b");
    }

    #[test]
    fn test_resolve_expr_dot() {
        let aliases = AliasMap::new();
        let scope: Vec<String> = vec!["myspec".into()];

        let expr = Expr::Dot {
            expr: Box::new(Expr::Var("vault".into())),
            field: "value".into(),
        };

        let resolved = resolve_expr(&aliases, &scope, expr);
        assert_eq!(resolved, Expr::Var("vault_value".into()));
        assert!(!has_dots(&resolved));
    }

    #[test]
    fn test_resolve_expr_nested_dot() {
        let aliases = AliasMap::new();
        let scope: Vec<String> = vec!["spec".into()];

        // target.vault.value → target_vault_value
        let expr = Expr::Dot {
            expr: Box::new(Expr::Dot {
                expr: Box::new(Expr::Var("target".into())),
                field: "vault".into(),
            }),
            field: "value".into(),
        };

        let resolved = resolve_expr(&aliases, &scope, expr);
        assert_eq!(resolved, Expr::Var("target_vault_value".into()));
    }

    #[test]
    fn test_resolve_expr_with_alias() {
        let mut aliases = AliasMap::new();
        aliases.insert("old_value".into(), "new_value".into());
        let scope: Vec<String> = vec![];

        let expr = Expr::Dot {
            expr: Box::new(Expr::Var("old".into())),
            field: "value".into(),
        };

        let resolved = resolve_expr(&aliases, &scope, expr);
        assert_eq!(resolved, Expr::Var("new_value".into()));
    }

    #[test]
    fn test_resolve_expr_preserves_binop() {
        let aliases = AliasMap::new();
        let scope: Vec<String> = vec![];

        let expr = Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Dot {
                expr: Box::new(Expr::Var("x".into())),
                field: "a".into(),
            }),
            right: Box::new(Expr::Lit(Val::Nat(2))),
        };

        let resolved = resolve_expr(&aliases, &scope, expr);
        assert!(!has_dots(&resolved));
        assert!(matches!(resolved, Expr::BinOp { .. }));
    }

    #[test]
    fn test_resolve_stmt_flow_assign() {
        let aliases = AliasMap::new();
        let scope: Vec<String> = vec![];

        let stmt = Stmt::FlowAssign {
            name: "vault.value".into(),
            op: FlowOp::Inflow,
            expr: Expr::Lit(Val::Nat(10)),
        };

        let resolved = resolve_stmt(&aliases, &scope, stmt);
        match &resolved {
            Stmt::FlowAssign { name, .. } => {
                assert_eq!(name, "vault.value"); // alias resolution only, no dot parsing
            }
            _ => panic!("expected FlowAssign"),
        }
        assert!(!stmt_has_dots(&resolved));
    }

    #[test]
    fn test_valid_in_state_func() {
        assert!(valid_in_state_func(&Stmt::Advance("open".into())));
        assert!(valid_in_state_func(&Stmt::Stay));
        assert!(valid_in_state_func(&Stmt::Call("fn".into())));

        assert!(!valid_in_state_func(&Stmt::FlowAssign {
            name: "x".into(),
            op: FlowOp::Assign,
            expr: Expr::Lit(Val::Nat(1)),
        }));

        // IfThenElse with valid branches
        assert!(valid_in_state_func(&Stmt::IfThenElse {
            cond: Expr::Lit(Val::Bool(true)),
            then_branch: vec![Stmt::Advance("a".into())],
            else_branch: vec![Stmt::Stay],
        }));

        // IfThenElse with invalid branch
        assert!(!valid_in_state_func(&Stmt::IfThenElse {
            cond: Expr::Lit(Val::Bool(true)),
            then_branch: vec![Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(1)),
            }],
            else_branch: vec![],
        }));
    }

    #[test]
    fn test_comp_well_formed() {
        let good = CompDef {
            name: "drain".into(),
            states: vec![
                (
                    "open".into(),
                    vec![Stmt::IfThenElse {
                        cond: Expr::Lit(Val::Bool(true)),
                        then_branch: vec![Stmt::Advance("close".into())],
                        else_branch: vec![],
                    }],
                ),
                ("close".into(), vec![Stmt::Stay]),
            ],
        };
        assert!(comp_well_formed(&good));

        let bad = CompDef {
            name: "broken".into(),
            states: vec![(
                "open".into(),
                vec![Stmt::FlowAssign {
                    name: "x".into(),
                    op: FlowOp::Assign,
                    expr: Expr::Lit(Val::Nat(1)),
                }],
            )],
        };
        assert!(!comp_well_formed(&bad));
    }

    #[test]
    fn test_resolve_spec() {
        let spec = Spec {
            name: "test".into(),
            constants: vec![],
            stocks: vec![StockDef {
                name: "s".into(),
                props: vec![("value".into(), Val::Nat(10))],
            }],
            flows: vec![],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: Some((3, vec![], vec![])),
        };

        let prog = resolve_spec(spec);
        assert_eq!(prog.rounds, 3);
        assert_eq!(prog.stocks.len(), 1);
        assert_eq!(prog.var_names, vec!["value"]);
        assert!(prog.components.is_empty());
    }

    #[test]
    fn test_merge_functions() {
        let spec1 = Spec {
            name: "a".into(),
            constants: vec![ConstDef {
                name: "c1".into(),
                value: Val::Nat(1),
                expr: None,
            }],
            stocks: vec![StockDef {
                name: "s1".into(),
                props: vec![("x".into(), Val::Nat(0))],
            }],
            flows: vec![],
            invariants: vec![Invariant::Assert {
                expr: Expr::Lit(Val::Bool(true)),
                temporal: Temporal::Always,
            }],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: None,
        };
        let spec2 = Spec {
            name: "b".into(),
            constants: vec![],
            stocks: vec![StockDef {
                name: "s2".into(),
                props: vec![("y".into(), Val::Nat(1))],
            }],
            flows: vec![],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: None,
        };
        let specs = vec![spec1, spec2];

        assert_eq!(merge_stocks(&specs).len(), 2);
        assert_eq!(merge_constants(&specs).len(), 1);
        assert_eq!(merge_invariants(&specs).len(), 1);
    }

    #[test]
    fn test_resolve_invariant() {
        let aliases = AliasMap::new();
        let scope: Vec<String> = vec![];

        let inv = Invariant::Assert {
            expr: Expr::Dot {
                expr: Box::new(Expr::Var("s".into())),
                field: "value".into(),
            },
            temporal: Temporal::Always,
        };

        let resolved = resolve_invariant(&aliases, &scope, inv);
        match &resolved {
            Invariant::Assert { expr, .. } => {
                assert!(!has_dots(expr));
                assert_eq!(*expr, Expr::Var("s_value".into()));
            }
            _ => panic!("expected Assert"),
        }
    }
}
