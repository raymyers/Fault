//! End-to-end integration tests for the Fault-lang/examples suite.
//!
//! Each test runs the full pipeline: parse → load imports → resolve → encode.
//! For fspec files we verify SMT structure. For fsystem files we test the
//! mixed statechart+flow encoding.

use fault_resolve::loader::{load_imports, load_system_imports};
use fault_resolve::{resolve_spec, resolve_system};
use fault_smt::encode_program;
use fault_syntax::parser::{parse_spec, parse_system};
use std::fs;
use std::path::{Path, PathBuf};

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("testdata")
        .join("examples")
}

/// Encode a .fspec example, returning (spec_name, smt_output).
fn encode_fspec(dir_name: &str, file_name: &str) -> (String, String) {
    let dir = examples_dir().join(dir_name);
    let src = fs::read_to_string(dir.join(file_name))
        .unwrap_or_else(|_| panic!("Missing {}/{}", dir_name, file_name));
    let mut spec = parse_spec(&src).unwrap_or_else(|e| panic!("{}: parse failed: {:?}", file_name, e));
    if !spec.import_decls.is_empty() {
        load_imports(&mut spec, &dir);
    }
    let name = spec.name.clone();
    let resolved = resolve_spec(spec);
    let smt = encode_program(&resolved, &name);
    (name, smt)
}

/// Encode a .fsystem example, returning (system_name, smt_output).
fn encode_fsystem(dir_name: &str, file_name: &str) -> (String, String) {
    let dir = examples_dir().join(dir_name);
    let src = fs::read_to_string(dir.join(file_name))
        .unwrap_or_else(|_| panic!("Missing {}/{}", dir_name, file_name));
    let mut sys = parse_system(&src).unwrap_or_else(|e| panic!("{}: parse failed: {:?}", file_name, e));
    load_system_imports(&mut sys, &dir);
    let name = sys.name.clone();
    let resolved = resolve_system(sys);
    let smt = encode_program(&resolved, &name);
    (name, smt)
}

fn count_decls(smt: &str) -> usize {
    smt.lines().filter(|l| l.trim().starts_with("(declare-fun")).count()
}

fn count_asserts(smt: &str) -> usize {
    smt.lines().filter(|l| l.trim().starts_with("(assert")).count()
}

fn has_var(smt: &str, var_prefix: &str) -> bool {
    smt.contains(var_prefix)
}

// ── .fspec examples ──────────────────────────────────────────────────

#[test]
fn example_sandwich() {
    let (name, smt) = encode_fspec("free-lunch", "sandwich.fspec");
    assert_eq!(name, "sandwich");
    assert!(smt.contains("(set-logic QF_NRA)"));
    assert!(count_decls(&smt) > 0, "should have declarations");
    assert!(count_asserts(&smt) > 0, "should have assertions");
    assert!(has_var(&smt, "sandwich_day_sandwiches_ham"));
}

#[test]
fn example_cache() {
    let (name, smt) = encode_fspec("cache", "cache.fspec");
    assert_eq!(name, "cache");
    assert!(has_var(&smt, "cache_r_machine_blocks"));
    assert!(has_var(&smt, "cache_r_machine_table"));
    // cache.fspec has assertions
    assert!(smt.contains("(assert"));
}

#[test]
fn example_cache_unkn() {
    let (name, smt) = encode_fspec("cache_unkn", "cache_unkn.fspec");
    assert_eq!(name, "cache");
    assert!(has_var(&smt, "cache_r_machine_blocks"));
    assert!(has_var(&smt, "cache_r_machine_table"));
}

#[test]
fn example_fibonacci() {
    let (name, smt) = encode_fspec("fibonacci", "fibonacci.fspec");
    assert_eq!(name, "fibonacci");
    assert!(has_var(&smt, "fibonacci_f"));
}

#[test]
fn example_orchestrator() {
    let (name, smt) = encode_fspec("orchestrator", "orchestrator.fspec");
    assert_eq!(name, "orchestrator");
    assert!(has_var(&smt, "orchestrator_cluster_p_instances"));
}

// ── .fsystem examples ────────────────────────────────────────────────

#[test]
fn example_drone() {
    let (name, smt) = encode_fsystem("drone", "drone.fsystem");
    assert_eq!(name, "drone");
    assert!(smt.contains("(set-logic QF_NRA)"));
    assert!(count_decls(&smt) > 10, "drone should have many declarations");
    assert!(has_var(&smt, "drone_frameMass"));
}

#[test]
fn example_repl() {
    let (name, smt) = encode_fsystem("repl", "repl.fsystem");
    assert_eq!(name, "repl");
    assert!(smt.contains("(set-logic QF_NRA)"));

    // Verify both imported spec flows appear
    assert!(has_var(&smt, "repl_record_machine_blocks"), "record flow stocks missing");
    assert!(has_var(&smt, "repl_record_machine_table"), "record flow stocks missing");
    assert!(has_var(&smt, "repl_manager_p_instances"), "manager flow stocks missing");
    assert!(has_var(&smt, "repl_manager_p_loading"), "manager flow stocks missing");

    // Verify statechart states
    assert!(has_var(&smt, "repl_replCache_idle"), "replCache states missing");
    assert!(has_var(&smt, "repl_replCache_lookupRecord"), "replCache states missing");
    assert!(has_var(&smt, "repl_containerMng_idle"), "containerMng states missing");

    // Verify assertions from imported specs are propagated
    assert!(smt.contains("repl_record_machine_blocks") && smt.contains("4.0"),
        "cache assertion about blocks < 4 missing");
    assert!(smt.contains("repl_manager_p_instances") && smt.contains("0.0"),
        "orchestrator assertion about instances > 0 missing");

    // Should have significant output (flow inlining produces many declarations)
    assert!(count_decls(&smt) >= 60, "expected at least 60 declarations, got {}", count_decls(&smt));
}

#[test]
fn example_repl_grouped_imports() {
    // Verify the parser correctly handles grouped import syntax
    let dir = examples_dir().join("repl");
    let src = fs::read_to_string(dir.join("repl.fsystem")).unwrap();
    let sys = parse_system(&src).unwrap();
    assert_eq!(sys.import_decls.len(), 2, "repl should have 2 imports");
    assert_eq!(sys.import_decls[0].alias, "cache");
    assert_eq!(sys.import_decls[1].alias, "orchestrator");
}
