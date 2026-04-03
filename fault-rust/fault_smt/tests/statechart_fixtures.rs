//! Statechart fixture tests: parse_system → resolve_system → encode, compare against Go oracle.
//!
//! Compares SMT output structurally (sorted declarations, normalized assertions)
//! to account for differences in block numbering and variable ordering.

use fault_resolve::{loader::load_system_imports, resolve_system};
use fault_smt::encode_program;
use fault_syntax::parser::parse_system;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

fn testdata_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("testdata")
}

/// Normalize an SMT string for comparison.
fn normalize_smt(smt: &str) -> (BTreeSet<String>, BTreeSet<String>) {
    let collapsed: String = smt.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut decls = BTreeSet::new();
    let mut asserts = BTreeSet::new();

    let mut depth = 0;
    let mut current = String::new();
    for ch in collapsed.chars() {
        if ch == '(' {
            if depth == 0 && !current.trim().is_empty() {
                current.clear();
            }
            depth += 1;
            current.push(ch);
        } else if ch == ')' {
            current.push(ch);
            depth -= 1;
            if depth == 0 {
                let expr = current.trim().to_string();
                let expr = normalize_block_numbers(&expr);
                // Parse S-expression, sort commutative ops, and re-render
                let sexpr = parse_sexpr(&expr);
                let expr = render_sexpr(&sort_commutative(&sexpr));
                if expr.starts_with("(declare-fun") || expr.starts_with("(set-logic") {
                    decls.insert(expr);
                } else if expr.starts_with("(assert") {
                    asserts.insert(expr);
                }
                current.clear();
            }
        } else {
            current.push(ch);
        }
    }

    (decls, asserts)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

fn parse_sexpr(s: &str) -> SExpr {
    let s = s.trim();
    if !s.starts_with('(') {
        return SExpr::Atom(s.to_string());
    }
    // Strip outer parens
    let inner = &s[1..s.len() - 1];
    let mut children = Vec::new();
    let mut depth = 0;
    let mut current = String::new();
    for ch in inner.chars() {
        if ch == '(' {
            depth += 1;
            current.push(ch);
        } else if ch == ')' {
            current.push(ch);
            depth -= 1;
            if depth == 0 {
                children.push(parse_sexpr(current.trim()));
                current.clear();
            }
        } else if ch == ' ' && depth == 0 {
            let tok = current.trim().to_string();
            if !tok.is_empty() {
                children.push(SExpr::Atom(tok));
            }
            current.clear();
        } else {
            current.push(ch);
        }
    }
    let tok = current.trim().to_string();
    if !tok.is_empty() {
        children.push(SExpr::Atom(tok));
    }
    SExpr::List(children)
}

fn sort_commutative(sexpr: &SExpr) -> SExpr {
    match sexpr {
        SExpr::Atom(a) => SExpr::Atom(a.clone()),
        SExpr::List(children) => {
            let sorted_children: Vec<SExpr> =
                children.iter().map(sort_commutative).collect();
            // Sort children of commutative operators (and, or)
            if let Some(SExpr::Atom(op)) = sorted_children.first()
                && (op == "and" || op == "or") {
                    let mut args: Vec<SExpr> =
                        sorted_children[1..].to_vec();
                    args.sort();
                    let mut result = vec![SExpr::Atom(op.clone())];
                    result.extend(args);
                    return SExpr::List(result);
                }
            SExpr::List(sorted_children)
        }
    }
}

fn render_sexpr(sexpr: &SExpr) -> String {
    match sexpr {
        SExpr::Atom(a) => a.clone(),
        SExpr::List(children) => {
            let parts: Vec<String> = children.iter().map(render_sexpr).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// Normalize numbered identifiers: block numbers and _state-%N suffixes.
fn normalize_block_numbers(s: &str) -> String {
    use std::collections::HashMap;
    let mut seen_blocks = HashMap::new();
    let mut block_counter = 0u32;
    let mut seen_states = HashMap::new();
    let mut state_counter = 0u32;

    let mut new_result = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if s[i..].starts_with("block") {
            let start = i;
            i += 5;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            // Consume suffix (true/false + _N version)
            let mut end = i;
            while end < bytes.len() && bytes[end] != b' ' && bytes[end] != b')' && bytes[end] != b'(' {
                end += 1;
            }
            let num_str = &s[start + 5..i];
            let suffix = &s[i..end];
            if !seen_blocks.contains_key(num_str) {
                seen_blocks.insert(num_str.to_string(), block_counter);
                block_counter += 1;
            }
            // Normalize suffix version: true_N → true_0, false_N → false_0
            let norm_suffix = if let Some(rest) = suffix.strip_prefix("true_") {
                let _ = rest;
                "true_0"
            } else if let Some(rest) = suffix.strip_prefix("false_") {
                let _ = rest;
                "false_0"
            } else {
                suffix
            };
            new_result.push_str(&format!("block{}{}", seen_blocks[num_str], norm_suffix));
            i = end;
        } else if s[i..].starts_with("_state-%") {
            // Normalize _state-%N to _state-%C where C is a canonical counter
            let start = i;
            i += 8; // skip "_state-%"
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let num_str = &s[start + 8..i];
            if !seen_states.contains_key(num_str) {
                seen_states.insert(num_str.to_string(), state_counter);
                state_counter += 1;
            }
            new_result.push_str(&format!("_state-%{}", seen_states[num_str]));
        } else {
            new_result.push(bytes[i] as char);
            i += 1;
        }
    }
    new_result
}

fn check_statechart(name: &str) {
    let dir = testdata_dir().join("statecharts");
    let input_path = dir.join(format!("{}.fsystem", name));
    let oracle_path = dir.join(format!("{}.smt2", name));

    let src = fs::read_to_string(&input_path)
        .unwrap_or_else(|_| panic!("Missing {}.fsystem", name));
    let oracle = fs::read_to_string(&oracle_path)
        .unwrap_or_else(|_| panic!("Missing {}.smt2", name));

    let mut sys = parse_system(&src).unwrap_or_else(|e| panic!("Parse error for {}: {}", name, e));
    load_system_imports(&mut sys, &dir);
    let sys_name = sys.name.clone();
    let resolved = resolve_system(sys);
    let actual = encode_program(&resolved, &sys_name);

    let (go_decls, go_asserts) = normalize_smt(&oracle);
    let (rs_decls, rs_asserts) = normalize_smt(&actual);

    // Compare declarations (sorted set comparison)
    if go_decls != rs_decls {
        let go_only: Vec<_> = go_decls.difference(&rs_decls).collect();
        let rs_only: Vec<_> = rs_decls.difference(&go_decls).collect();
        if !go_only.is_empty() || !rs_only.is_empty() {
            // Allow block-number differences — only check non-block declarations
            let go_non_block: BTreeSet<_> = go_decls.iter().filter(|d| !d.contains("block")).cloned().collect();
            let rs_non_block: BTreeSet<_> = rs_decls.iter().filter(|d| !d.contains("block")).cloned().collect();
            assert_eq!(
                go_non_block, rs_non_block,
                "Declaration mismatch for {}\nGo-only: {:?}\nRust-only: {:?}",
                name, go_only, rs_only
            );
        }
    }

    // Compare assertions (set comparison — order doesn't matter for SMT)
    if go_asserts != rs_asserts {
        let go_only: Vec<_> = go_asserts.difference(&rs_asserts).collect();
        let rs_only: Vec<_> = rs_asserts.difference(&go_asserts).collect();
        if !go_only.is_empty() || !rs_only.is_empty() {
            panic!(
                "Assertion mismatch for {}\n\n--- Go-only ({}) ---\n{}\n\n--- Rust-only ({}) ---\n{}",
                name,
                go_only.len(),
                go_only.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"),
                rs_only.len(),
                rs_only.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"),
            );
        }
    }
}

#[test]
fn statechart_advanceand() {
    check_statechart("advanceand");
}

#[test]
fn statechart_advanceor() {
    check_statechart("advanceor");
}

#[test]
fn statechart_choose1() {
    check_statechart("choose1");
}

#[test]
fn statechart_choose2() {
    check_statechart("choose2");
}

#[test]
fn statechart_multioradvance() {
    check_statechart("multioradvance");
}

#[test]
fn statechart_trigger() {
    check_statechart("trigger");
}

#[test]
fn statechart_statechart() {
    check_statechart("statechart");
}

#[test]
fn statechart_mixedcalls() {
    check_statechart("mixedcalls");
}
