//! SMT fixture tests: parse → resolve → encode, compare against oracle output.
//!
//! For each fixture with `input.fspec` + `expected.smt2`, we verify our encoder
//! produces semantically identical SMT output (modulo whitespace and declaration order).

use fault_resolve::loader::load_imports;
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

    // Run again to verify determinism (BTreeMap ensures consistent ordering).
    let actual2 = encode_program(&resolve_spec(parse_spec(&input).unwrap()), &spec_name);
    let (_, asserts2) = normalize(&actual2);
    let mut sorted1 = asserts.clone();
    sorted1.sort();
    let mut sorted2 = asserts2;
    sorted2.sort();
    assert_eq!(
        sorted1, sorted2,
        "{}: assertion sets differ across runs",
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

// ── Import fixtures ────────────────────────────────────────────────
// These load imports from disk, then parse → load → resolve → encode.

/// Run the import pipeline on an `.fspec` file in testdata/imports/.
/// Compares against an `.smt2` oracle file next to it.
/// Normalize an SMT string by stripping all whitespace (for Go oracle comparison).
fn strip_ws(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

fn check_import_fixture(fspec_name: &str, smt2_name: &str) {
    let imports_dir = fixture_dir().join("imports");
    let input_path = imports_dir.join(fspec_name);
    let input = fs::read_to_string(&input_path)
        .unwrap_or_else(|_| panic!("Missing imports/{}", fspec_name));

    let mut spec =
        parse_spec(&input).unwrap_or_else(|e| panic!("{}: parse failed: {:?}", fspec_name, e));

    if !spec.import_decls.is_empty() {
        load_imports(&mut spec, &imports_dir);
    }

    let spec_name = spec.name.clone();
    let resolved = resolve_spec(spec);
    let actual = encode_program(&resolved, &spec_name);

    let expected_path = imports_dir.join(smt2_name);
    let expected = fs::read_to_string(&expected_path)
        .unwrap_or_else(|_| panic!("Missing imports/{}", smt2_name));

    // Extract declarations and assertions from both, stripping whitespace
    let (act_decls, act_asserts) = normalize(&actual);
    let (exp_decls, exp_asserts) = normalize(&expected);

    let mut act_d: Vec<String> = act_decls.iter().map(|s| strip_ws(s)).collect();
    act_d.sort();
    let mut exp_d: Vec<String> = exp_decls.iter().map(|s| strip_ws(s)).collect();
    exp_d.sort();
    assert_eq!(
        act_d, exp_d,
        "imports/{}: declaration mismatch\nactual:\n{}\nexpected:\n{}",
        fspec_name, actual, expected
    );

    // Compare assertions as whitespace-stripped sorted sets
    let mut act_a: Vec<String> = act_asserts.iter().map(|s| strip_ws(s)).collect();
    act_a.sort();
    let mut exp_a: Vec<String> = exp_asserts.iter().map(|s| strip_ws(s)).collect();
    exp_a.sort();
    assert_eq!(
        act_a, exp_a,
        "imports/{}: assertion mismatch\nactual:\n{}\nexpected:\n{}",
        fspec_name, actual, expected
    );
}

#[test]
fn fixture_single_import() {
    check_import_fixture("single_import.fspec", "single_import.smt2");
}

#[test]
fn fixture_renamed_import() {
    check_import_fixture("renamed_import.fspec", "renamed_import.smt2");
}

#[test]
fn fixture_circle_import() {
    check_import_fixture("circle_import1.fspec", "circle_import.smt2");
}
