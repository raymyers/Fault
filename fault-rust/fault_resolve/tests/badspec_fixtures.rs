//! Data-driven tests for bad spec error detection.
//! Verifies that the validator catches known-bad specs.

use fault_resolve::validate::{FaultError, validate_spec};
use fault_syntax::parser::parse_spec;
use std::fs;
use std::path::Path;

fn badspec_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("testdata")
        .join("badspecs")
        .leak()
}

fn read_and_validate(name: &str) -> Vec<FaultError> {
    let path = badspec_dir().join(name);
    let src = fs::read_to_string(&path).unwrap_or_else(|_| panic!("Missing badspecs/{}", name));
    let spec = parse_spec(&src).unwrap_or_else(|e| panic!("{}: parse failed: {:?}", name, e));
    validate_spec(&spec)
}

#[test]
fn badspec_zerounds() {
    let errs = read_and_validate("zerounds.fspec");
    assert!(
        errs.iter().any(|e| matches!(e, FaultError::ZeroRounds)),
        "expected ZeroRounds error, got: {:?}",
        errs
    );
}

#[test]
fn badspec_emptyfunc() {
    let errs = read_and_validate("emptyfunc.fspec");
    assert!(
        errs.iter()
            .any(|e| matches!(e, FaultError::EmptyFunction { .. })),
        "expected EmptyFunction error, got: {:?}",
        errs
    );
}

#[test]
fn badspec_nodefs() {
    let errs = read_and_validate("nodefs.fspec");
    assert!(
        errs.iter()
            .any(|e| matches!(e, FaultError::MissingRunBlock)),
        "expected MissingRunBlock error, got: {:?}",
        errs
    );
}

#[test]
fn badspec_doubleswap() {
    let errs = read_and_validate("doubleswap.fspec");
    assert!(
        errs.iter()
            .any(|e| matches!(e, FaultError::DoubleSwap { .. })),
        "expected DoubleSwap error, got: {:?}",
        errs
    );
}

#[test]
fn badspec_aliaschain() {
    let errs = read_and_validate("aliaschain.fspec");
    assert!(
        errs.iter()
            .any(|e| matches!(e, FaultError::DoubleSwap { .. })),
        "expected DoubleSwap error for alias chain, got: {:?}",
        errs
    );
}

#[test]
fn badspec_sharedstate_is_valid() {
    let errs = read_and_validate("sharedstate.fspec");
    assert!(
        errs.is_empty(),
        "sharedstate should be valid, got errors: {:?}",
        errs
    );
}

#[test]
fn badspec_flows_no_run_block() {
    let errs = read_and_validate("flowsnorun.fspec");
    assert!(
        errs.iter().any(|e| matches!(e, FaultError::MissingRunBlock)),
        "expected MissingRunBlock for flows without run block, got: {:?}",
        errs
    );
}

#[test]
fn badspec_stocks_no_run_block() {
    let errs = read_and_validate("stocksnorun.fspec");
    assert!(
        errs.iter().any(|e| matches!(e, FaultError::MissingRunBlock)),
        "expected MissingRunBlock for stocks without run block, got: {:?}",
        errs
    );
}

#[test]
fn badspec_empty_spec() {
    let errs = read_and_validate("emptyspec.fspec");
    assert!(
        errs.iter().any(|e| matches!(e, FaultError::MissingRunBlock)),
        "expected MissingRunBlock for empty spec, got: {:?}",
        errs
    );
}

#[test]
fn badspec_consts_only_is_valid() {
    let errs = read_and_validate("constsonly.fspec");
    assert!(
        errs.is_empty(),
        "constants-only spec should be valid, got errors: {:?}",
        errs
    );
}
