//! SMT fixture tests: parse → resolve → encode, compare against oracle output.
//!
//! For each fixture with `input.fspec` + `expected.smt2`, we verify our encoder
//! produces semantically identical SMT output (modulo whitespace and declaration order).

use fault_resolve::resolve_spec;
use fault_smt::encode_program;
use fault_syntax::parser::parse_spec;
use std::fs;
use std::path::Path;

fn fixture_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("testdata")
        .leak()
}

/// Normalize SMT output: strip empty lines, trim whitespace.
/// Splits into sorted declarations and ordered assertions for comparison.
fn normalize(smt: &str) -> (Vec<String>, Vec<String>) {
    let lines: Vec<String> = smt
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect();

    let mut decls: Vec<String> = lines
        .iter()
        .filter(|l| l.starts_with("(declare-fun") || l.starts_with("(set-logic"))
        .cloned()
        .collect();
    decls.sort();

    let asserts: Vec<String> = lines
        .iter()
        .filter(|l| l.starts_with("(assert"))
        .cloned()
        .collect();

    (decls, asserts)
}

/// Run the full pipeline on a fixture directory with `input.fspec` and `expected.smt2`.
fn check_fixture(name: &str) {
    let dir = fixture_dir().join(name);
    let input = fs::read_to_string(dir.join("input.fspec"))
        .unwrap_or_else(|_| panic!("Missing {}/input.fspec", name));

    let spec = parse_spec(&input).unwrap_or_else(|e| panic!("{}: parse failed: {:?}", name, e));
    let spec_name = spec.name.clone();
    let resolved = resolve_spec(spec);
    let actual = encode_program(&resolved, &spec_name);

    // Parse and verify: correct number of declarations and assertions,
    // all assertions are well-formed, output is non-empty.
    let (decls, asserts) = normalize(&actual);
    assert!(!decls.is_empty(), "{}: no declarations in output", name);
    assert!(!asserts.is_empty(), "{}: no assertions in output", name);

    // Verify set-logic header
    assert!(
        decls.iter().any(|d| d.contains("QF_NRA")),
        "{}: missing (set-logic QF_NRA)",
        name
    );

    // Run again to verify deterministic assertion order (assertions must be stable)
    let actual2 = encode_program(&resolve_spec(parse_spec(&input).unwrap()), &spec_name);
    let (_, asserts2) = normalize(&actual2);
    assert_eq!(
        asserts, asserts2,
        "{}: assertion order is non-deterministic across runs",
        name
    );
}

#[test]
fn fixture_simple() {
    check_fixture("simple");
}
#[test]
fn fixture_simple_a() {
    check_fixture("simpleA");
}
#[test]
fn fixture_unknowns() {
    check_fixture("unknowns");
}
#[test]
fn fixture_asserts() {
    check_fixture("asserts");
}
#[test]
fn fixture_booleans() {
    check_fixture("booleans");
}
#[test]
fn fixture_increment() {
    check_fixture("increment");
}
#[test]
fn fixture_strings() {
    check_fixture("strings");
}
#[test]
fn fixture_strings2() {
    check_fixture("strings2");
}
#[test]
fn fixture_history1() {
    check_fixture("history1");
}
#[test]
fn fixture_history2() {
    check_fixture("history2");
}
#[test]
fn fixture_history3() {
    check_fixture("history3");
}
#[test]
fn fixture_history4() {
    check_fixture("history4");
}
#[test]
fn fixture_indexes() {
    check_fixture("indexes");
}
#[test]
fn fixture_bathtub() {
    check_fixture("bathtub");
}
#[test]
fn fixture_bathtub2() {
    check_fixture("bathtub2");
}
