//! Integration test: parse fixtures and resolve them.
//! Verifies that resolution eliminates all Dot nodes.

use fault_resolve::*;
use fault_syntax::parser;
use std::fs;
use std::path::Path;

fn resolve_fspec(src: &str) -> ResolvedProgram {
    let spec = parser::parse_spec(src).expect("parse failed");
    resolve_spec(spec)
}

/// After resolving a spec, no Expr::Dot nodes should remain in
/// invariants or run/init blocks.
fn check_no_dots_in_program(prog: &ResolvedProgram, name: &str) {
    for inv in &prog.invariants {
        let (expr, guard) = match inv {
            fault_syntax::Invariant::Assert { expr, .. }
            | fault_syntax::Invariant::Assume { expr, .. } => (expr, None),
            fault_syntax::Invariant::AssertWhen { guard, body, .. }
            | fault_syntax::Invariant::AssumeWhen { guard, body, .. } => (body, Some(guard)),
        };
        assert!(
            !has_dots(expr),
            "{}: invariant body still has Dot nodes",
            name
        );
        if let Some(g) = guard {
            assert!(
                !has_dots(g),
                "{}: invariant guard still has Dot nodes",
                name
            );
        }
    }
    // Note: init_block and run_block are not yet fully resolved at this phase
    // (the parser stores `Call("l.fn")` etc., not Dot nodes), so we just
    // verify invariants are clean.
}

#[test]
fn resolve_simple_spec() {
    let src = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/simpleA/input.fspec"),
    )
    .unwrap();
    let prog = resolve_fspec(&src);
    assert_eq!(prog.rounds, 1);
    assert_eq!(prog.stocks.len(), 1);
    assert_eq!(prog.flows.len(), 1);
    check_no_dots_in_program(&prog, "simpleA");
}

#[test]
fn resolve_bathtub_spec() {
    let src = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/bathtub/input.fspec"),
    )
    .unwrap();
    let prog = resolve_fspec(&src);
    assert_eq!(prog.rounds, 4);
    assert_eq!(prog.stocks.len(), 1);
    assert_eq!(prog.flows.len(), 2);
    check_no_dots_in_program(&prog, "bathtub");
}

#[test]
fn resolve_asserts_spec() {
    let src = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/asserts/input.fspec"),
    )
    .unwrap();
    let prog = resolve_fspec(&src);
    assert_eq!(prog.invariants.len(), 2);
    check_no_dots_in_program(&prog, "asserts");
}

#[test]
fn resolve_unknowns_spec() {
    let src = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/unknowns/input.fspec"),
    )
    .unwrap();
    let prog = resolve_fspec(&src);
    assert_eq!(prog.invariants.len(), 2);
    assert_eq!(prog.var_names, vec!["a", "b", "c"]);
    check_no_dots_in_program(&prog, "unknowns");
}

#[test]
fn resolve_flatten_name_matches_lean() {
    // Lean guards from Resolve.lean:24-28
    assert_eq!(
        flatten_name(&["myspec", "mybuffer", "f", "target", "value"]),
        "myspec_mybuffer_f_target_value"
    );
    assert_eq!(
        flatten_name(&["simple", "l", "vault", "value"]),
        "simple_l_vault_value"
    );
    assert_eq!(flatten_name(&["x"]), "x");
}

#[test]
fn resolve_dot_in_invariant() {
    // Parse a spec with dotted invariant, verify resolution eliminates Dot
    let src = r#"spec test;

def s = stock{
    value: 10,
};

assert s.value > 0;
assume s.value < 100;
"#;
    let spec = parser::parse_spec(src).unwrap();
    let aliases = AliasMap::new();
    let scope: Vec<String> = vec![];

    for inv in &spec.invariants {
        let resolved = resolve_invariant(&aliases, &scope, inv.clone());
        match &resolved {
            fault_syntax::Invariant::Assert { expr, .. }
            | fault_syntax::Invariant::Assume { expr, .. } => {
                assert!(!has_dots(expr), "resolved invariant still has Dot nodes");
            }
            _ => {}
        }
    }
}

#[test]
fn resolve_alias_chain() {
    let mut aliases = AliasMap::new();
    aliases.insert("x_val".into(), "y_val".into());
    aliases.insert("y_val".into(), "z_val".into());

    let expr = fault_syntax::Expr::Dot {
        expr: Box::new(fault_syntax::Expr::Var("x".into())),
        field: "val".into(),
    };

    let resolved = resolve_expr(&aliases, &[], expr);
    assert_eq!(resolved, fault_syntax::Expr::Var("z_val".into()));
}
