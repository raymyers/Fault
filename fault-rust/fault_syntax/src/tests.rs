use crate::*;

/// Hand-written AST for simple.fspec:
///
/// ```text
/// spec simple;
///
/// def st = stock{ value: 30 };
/// def fl = flow{
///     vault: new st,
///     fn: func{
///         if vault.value > 4 {
///            vault.value <- vault.value - 2;
///         }
///     },
/// };
///
/// for 1 init{l = new fl;} run { l.fn; }
/// ```
fn simple_spec() -> Spec {
    Spec {
        name: "simple".into(),
        constants: vec![],
        stocks: vec![StockDef {
            name: "st".into(),
            props: vec![("value".into(), Val::Nat(30))],
        }],
        flows: vec![FlowDef {
            name: "fl".into(),
            stocks: vec![("vault".into(), "st".into())],
            funcs: vec![(
                "fn".into(),
                vec![Stmt::IfThenElse {
                    cond: Expr::BinOp {
                        op: BinOp::Gt,
                        left: Box::new(Expr::Dot {
                            expr: Box::new(Expr::Var("vault".into())),
                            field: "value".into(),
                        }),
                        right: Box::new(Expr::Lit(Val::Nat(4))),
                    },
                    then_branch: vec![Stmt::FlowAssign {
                        name: "vault.value".into(),
                        op: FlowOp::Inflow,
                        expr: Expr::BinOp {
                            op: BinOp::Sub,
                            left: Box::new(Expr::Dot {
                                expr: Box::new(Expr::Var("vault".into())),
                                field: "value".into(),
                            }),
                            right: Box::new(Expr::Lit(Val::Nat(2))),
                        },
                    }],
                    else_branch: vec![],
                }],
            )],
        }],
        invariants: vec![],
        import_decls: vec![],
        imported_specs: vec![],
        run_block: Some((
            1,
            vec![Stmt::Call("fl".into())],
            vec![Stmt::Call("fl.fn".into())],
        )),
    }
}

#[test]
fn val_json_roundtrip() {
    let vals = vec![
        Val::Nat(42),
        Val::Float(3.14),
        Val::Bool(true),
        Val::Str("hello".into()),
        Val::Unknown,
        Val::Uncertain {
            mean: 10.0,
            sigma: 2.5,
        },
        Val::Nil,
    ];
    for val in &vals {
        let json = serde_json::to_string(val).unwrap();
        let back: Val = serde_json::from_str(&json).unwrap();
        assert_eq!(*val, back);
    }
}

#[test]
fn expr_json_roundtrip() {
    let expr = Expr::BinOp {
        op: BinOp::Add,
        left: Box::new(Expr::Var("x".into())),
        right: Box::new(Expr::Lit(Val::Nat(1))),
    };
    let json = serde_json::to_string(&expr).unwrap();
    let back: Expr = serde_json::from_str(&json).unwrap();
    assert_eq!(expr, back);
}

#[test]
fn spec_json_roundtrip() {
    let spec = simple_spec();
    let json = serde_json::to_string_pretty(&spec).unwrap();
    let back: Spec = serde_json::from_str(&json).unwrap();
    assert_eq!(spec, back);
}

#[test]
fn system_json_roundtrip() {
    let sys = System {
        name: "test_sys".into(),
        imports: vec![],
        import_decls: vec![],
        globals: vec![],
        components: vec![CompDef {
            name: "ctrl".into(),
            states: vec![("on".into(), vec![Stmt::Advance("off".into())])],
        }],
        invariants: vec![Invariant::Assert {
            expr: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(0))),
            },
            temporal: Temporal::Always,
        }],
        start_states: vec![("ctrl".into(), "on".into())],
        run_block: Some((5, vec![], vec![Stmt::Call("f".into())])),
    };
    let json = serde_json::to_string_pretty(&sys).unwrap();
    let back: System = serde_json::from_str(&json).unwrap();
    assert_eq!(sys, back);
}

#[test]
fn all_invariant_variants_roundtrip() {
    let invariants = vec![
        Invariant::Assert {
            expr: Expr::Var("x".into()),
            temporal: Temporal::Always,
        },
        Invariant::Assume {
            expr: Expr::Var("y".into()),
            temporal: Temporal::Eventually,
        },
        Invariant::AssertWhen {
            guard: Expr::Var("g".into()),
            body: Expr::Var("b".into()),
            temporal: Temporal::EventuallyAlways,
        },
        Invariant::AssumeWhen {
            guard: Expr::Var("g".into()),
            body: Expr::Var("b".into()),
            temporal: Temporal::Nmt(3),
        },
    ];
    for inv in &invariants {
        let json = serde_json::to_string(inv).unwrap();
        let back: Invariant = serde_json::from_str(&json).unwrap();
        assert_eq!(*inv, back);
    }
}

#[test]
fn all_stmt_variants_roundtrip() {
    let stmts = vec![
        Stmt::FlowAssign {
            name: "x".into(),
            op: FlowOp::Assign,
            expr: Expr::Lit(Val::Nat(1)),
        },
        Stmt::IfThenElse {
            cond: Expr::Lit(Val::Bool(true)),
            then_branch: vec![Stmt::Stay],
            else_branch: vec![Stmt::Advance("s2".into())],
        },
        Stmt::Call("fn1".into()),
        Stmt::Advance("s1".into()),
        Stmt::Stay,
        Stmt::Seq(vec![Stmt::Stay]),
        Stmt::Parallel(vec![Stmt::Stay, Stmt::Call("fn2".into())]),
    ];
    for stmt in &stmts {
        let json = serde_json::to_string(stmt).unwrap();
        let back: Stmt = serde_json::from_str(&json).unwrap();
        assert_eq!(*stmt, back);
    }
}

#[test]
fn all_expr_variants_roundtrip() {
    let exprs = vec![
        Expr::Lit(Val::Nat(42)),
        Expr::Var("x".into()),
        Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Lit(Val::Nat(1))),
            right: Box::new(Expr::Lit(Val::Nat(2))),
        },
        Expr::UnOp {
            op: UnOp::Neg,
            expr: Box::new(Expr::Var("y".into())),
        },
        Expr::Dot {
            expr: Box::new(Expr::Var("vault".into())),
            field: "value".into(),
        },
        Expr::History {
            name: "x".into(),
            offset: -1,
        },
        Expr::Choose(vec![Expr::Lit(Val::Nat(1)), Expr::Lit(Val::Nat(2))]),
    ];
    for expr in &exprs {
        let json = serde_json::to_string(expr).unwrap();
        let back: Expr = serde_json::from_str(&json).unwrap();
        assert_eq!(*expr, back);
    }
}

#[test]
fn temporal_variants_roundtrip() {
    let temps = vec![
        Temporal::Always,
        Temporal::Eventually,
        Temporal::EventuallyAlways,
        Temporal::Nmt(5),
        Temporal::Nft(3),
    ];
    for t in &temps {
        let json = serde_json::to_string(t).unwrap();
        let back: Temporal = serde_json::from_str(&json).unwrap();
        assert_eq!(*t, back);
    }
}

/// Verify a full spec snapshot can deserialize from a known JSON string.
#[test]
fn spec_snapshot_from_json() {
    let spec = simple_spec();
    let snapshot = serde_json::to_string_pretty(&spec).unwrap();

    // Deserialize from the snapshot
    let back: Spec = serde_json::from_str(&snapshot).unwrap();
    assert_eq!(spec, back);
    assert_eq!(back.name, "simple");
    assert_eq!(back.stocks.len(), 1);
    assert_eq!(back.flows.len(), 1);
    assert_eq!(back.invariants.len(), 0);
    assert!(back.run_block.is_some());
    let (rounds, _, _) = back.run_block.unwrap();
    assert_eq!(rounds, 1);
}
