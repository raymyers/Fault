//! Parse Z3 model output and format human-readable counterexample traces.
//!
//! Two formatting modes:
//! 1. **Event-log replay** (`format_from_event_log`): Uses the event log recorded
//!    during SMT encoding to produce Go-style round-based output with function
//!    call nesting and variable transitions.
//! 2. **Fallback** (`format_counterexample_flat`): When no event log is available
//!    (e.g., statechart-only specs), groups SSA variables by base name.

use std::collections::BTreeMap;

use fault_smt::event_log::{Event, EventLog};

// ── Z3 model parser ─────────────────────────────────────────────────────

/// Parse Z3 `(model (define-fun …) …)` output into name → value pairs.
pub fn parse_model(raw: &str) -> BTreeMap<String, String> {
    let mut result = BTreeMap::new();
    let mut chars = raw.chars().peekable();

    while let Some(&ch) = chars.peek() {
        if ch == '(' {
            let rest: String = chars.clone().take(11).collect();
            if rest == "(define-fun" {
                for _ in 0..11 {
                    chars.next();
                }
                skip_ws(&mut chars);
                let name = read_symbol(&mut chars);
                skip_ws(&mut chars);
                expect_char(&mut chars, '(');
                expect_char(&mut chars, ')');
                skip_ws(&mut chars);
                let _type = read_symbol(&mut chars);
                skip_ws(&mut chars);
                let value_raw = read_value(&mut chars);
                skip_ws(&mut chars);
                if chars.peek() == Some(&')') {
                    chars.next();
                }
                let value = eval_value(&value_raw);
                result.insert(name, value);
            } else {
                chars.next();
            }
        } else {
            chars.next();
        }
    }
    result
}

// ── Internal variable filter ─────────────────────────────────────────────

/// Identify internal solver variables that should be hidden from the user.
pub fn is_internal(name: &str) -> bool {
    if name.starts_with("@__run") {
        return true;
    }
    if name
        .strip_prefix("block")
        .is_some_and(|rest| rest.contains("true") || rest.contains("false"))
    {
        return true;
    }
    if name.contains("__state-%") {
        return true;
    }
    false
}

// ── SSA helpers ──────────────────────────────────────────────────────────

/// Split "foo_bar_3" → ("foo_bar", 3). Returns None if no SSA suffix.
fn split_ssa(name: &str) -> Option<(&str, u32)> {
    let idx = name.rfind('_')?;
    let n: u32 = name[idx + 1..].parse().ok()?;
    Some((&name[..idx], n))
}

/// Get the base name (strip trailing `_N` SSA suffix).
fn get_base(ssa_name: &str) -> &str {
    split_ssa(ssa_name).map_or(ssa_name, |(base, _)| base)
}

/// Strip spec-name prefix: "asserts_test_value" → "test_value".
fn strip_spec_prefix<'a>(name: &'a str, spec_name: &str) -> &'a str {
    let prefix = format!("{}_", spec_name);
    name.strip_prefix(&prefix).unwrap_or(name)
}

// ── Event-log–based formatter (matches Go's Logger.Print()) ─────────────

/// Format a counterexample by replaying the event log with Z3 results.
///
/// Produces output matching the Go implementation:
/// ```text
/// Start model, run for 5 rounds
/// -----------------------------------
///    Run function cache_r_store (round 1)
///       Set variable cache_r_machine_blocks to value 0.0
///       cache_r_machine_table: 0.0 → 1.0
///       Variable cache_r_machine_blocks is still 0.0
/// ```
pub fn format_from_event_log(log: &EventLog) -> String {
    let mut out = String::new();
    let mut indent = String::new();
    // Track current values for showing transitions
    let mut current_state: BTreeMap<String, String> = BTreeMap::new();

    for event in &log.events {
        match event {
            Event::RunStart { rounds } => {
                out.push('\n');
                out.push_str(&format!("Start model, run for {} rounds\n", rounds));
                out.push_str("-----------------------------------\n");
                indent.push_str("   ");
            }
            Event::FunctionEntry { name, round } => {
                out.push_str(&format!("{}Run function {} (round {})\n", indent, name, round));
                indent.push_str("   ");
            }
            Event::FunctionExit { .. } => {
                if indent.len() >= 3 {
                    indent.truncate(indent.len() - 3);
                }
            }
            Event::VariableUpdate { ssa_name } => {
                if is_internal(ssa_name) {
                    continue;
                }
                let base = get_base(ssa_name);
                let new_value = log
                    .results
                    .get(ssa_name)
                    .map(|s| s.as_str())
                    .unwrap_or("?");

                if let Some(old_value) = current_state.get(base) {
                    if old_value == new_value {
                        out.push_str(&format!(
                            "{}Variable {} is still {}\n",
                            indent, base, new_value
                        ));
                    } else {
                        out.push_str(&format!(
                            "{}{}: {} → {}\n",
                            indent, base, old_value, new_value
                        ));
                    }
                } else {
                    out.push_str(&format!(
                        "{}Set variable {} to value {}\n",
                        indent, base, new_value
                    ));
                }
                current_state.insert(base.to_string(), new_value.to_string());
            }
            Event::Solvable { ssa_name } => {
                if is_internal(ssa_name) {
                    continue;
                }
                let base = get_base(ssa_name);
                let value = log
                    .results
                    .get(ssa_name)
                    .map(|s| s.as_str())
                    .unwrap_or("?");
                out.push_str(&format!(
                    "{}Resolving variable {} to value {}\n",
                    indent, base, value
                ));
                current_state.insert(base.to_string(), value.to_string());
            }
        }
    }
    out.push('\n');
    out
}

// ── Flat fallback formatter ──────────────────────────────────────────────

/// Flat format for when no event log is available (statechart-only specs).
pub fn format_counterexample_flat(
    model: &BTreeMap<String, String>,
    spec_name: &str,
) -> String {
    let mut out = String::from("COUNTEREXAMPLE FOUND\n");
    out.push_str("The following assertion can be violated:\n\n");

    let mut groups: BTreeMap<String, Vec<(u32, String)>> = BTreeMap::new();
    let mut constants: BTreeMap<String, String> = BTreeMap::new();

    for (name, value) in model {
        if is_internal(name) {
            continue;
        }
        let display_name = strip_spec_prefix(name, spec_name);
        if let Some((base, idx)) = split_ssa(display_name) {
            groups.entry(base.to_string()).or_default().push((idx, value.clone()));
        } else {
            constants.insert(display_name.to_string(), value.clone());
        }
    }

    for (name, value) in &constants {
        out.push_str(&format!("  {} = {}\n", name, value));
    }
    if !constants.is_empty() {
        out.push('\n');
    }

    for (base, mut steps) in groups {
        steps.sort_by_key(|(idx, _)| *idx);
        out.push_str(&format!("  {}\n", base));
        let mut prev: Option<&str> = None;
        for (idx, val) in &steps {
            match prev {
                Some(p) if p == val => {}
                Some(p) => {
                    out.push_str(&format!("    step {}: {} → {}\n", idx, p, val));
                }
                None => {
                    out.push_str(&format!("    step {}: {}\n", idx, val));
                }
            }
            prev = Some(val);
        }
        out.push('\n');
    }
    out
}

/// Main entry point: format a counterexample using the event log if available,
/// otherwise fall back to flat display.
pub fn format_counterexample(
    model: &BTreeMap<String, String>,
    event_log: &mut EventLog,
) -> String {
    // Use event log only if it has real content (function calls or variable updates)
    let has_real_events = event_log.events.iter().any(|e| {
        matches!(
            e,
            Event::FunctionEntry { .. }
                | Event::VariableUpdate { .. }
                | Event::Solvable { .. }
        )
    });

    if !has_real_events {
        return format_counterexample_flat(model, &event_log.spec_name);
    }

    // Populate event log results from Z3 model
    event_log.results.clone_from(model);
    format_from_event_log(event_log)
}

// ── S-expression parser helpers ──────────────────────────────────────────

fn skip_ws(chars: &mut std::iter::Peekable<std::str::Chars>) {
    while chars.peek().is_some_and(|c| c.is_whitespace()) {
        chars.next();
    }
}

fn expect_char(chars: &mut std::iter::Peekable<std::str::Chars>, expected: char) {
    if chars.peek() == Some(&expected) {
        chars.next();
    }
}

fn read_symbol(chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
    let mut s = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() || c == '(' || c == ')' {
            break;
        }
        s.push(c);
        chars.next();
    }
    s
}

fn read_value(chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
    skip_ws(chars);
    if chars.peek() == Some(&'(') {
        read_sexpr(chars)
    } else {
        read_symbol(chars)
    }
}

fn read_sexpr(chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
    let mut s = String::new();
    let mut depth = 0;
    while let Some(&c) = chars.peek() {
        s.push(c);
        chars.next();
        if c == '(' {
            depth += 1;
        } else if c == ')' {
            depth -= 1;
            if depth == 0 {
                break;
            }
        }
    }
    s
}

/// Evaluate a Z3 value expression to a human-readable string.
fn eval_value(s: &str) -> String {
    let s = s.trim();
    if !s.starts_with('(') {
        return s.to_string();
    }
    let inner = &s[1..s.len() - 1].trim();
    let parts: Vec<&str> = inner.split_whitespace().collect();

    match parts.as_slice() {
        ["-", val] => {
            if let Ok(v) = val.parse::<f64>() {
                format_float(-v)
            } else {
                format!("-{}", val)
            }
        }
        ["/", a, b] => {
            if let (Ok(va), Ok(vb)) = (a.parse::<f64>(), b.parse::<f64>()) {
                if vb != 0.0 { format_float(va / vb) } else { s.to_string() }
            } else {
                s.to_string()
            }
        }
        ["*", a, b] => eval_binop(a, b, |x, y| x * y, s),
        ["+", a, b] => eval_binop(a, b, |x, y| x + y, s),
        ["-", a, b] => eval_binop(a, b, |x, y| x - y, s),
        _ => s.to_string(),
    }
}

fn eval_binop(a: &str, b: &str, f: fn(f64, f64) -> f64, fallback: &str) -> String {
    if let (Ok(va), Ok(vb)) = (a.parse::<f64>(), b.parse::<f64>()) {
        format_float(f(va, vb))
    } else {
        fallback.to_string()
    }
}

fn format_float(v: f64) -> String {
    if v == v.trunc() {
        format!("{:.1}", v)
    } else {
        format!("{}", v)
    }
}

// ── Tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // -- Parser tests --

    #[test]
    fn parse_simple_reals() {
        let raw = r#"(model
  (define-fun x () Real 40.0)
  (define-fun y () Real 20.0)
)"#;
        let model = parse_model(raw);
        assert_eq!(model["x"], "40.0");
        assert_eq!(model["y"], "20.0");
    }

    #[test]
    fn parse_booleans() {
        let raw = r#"(model
  (define-fun a () Bool true)
  (define-fun b () Bool false)
)"#;
        let model = parse_model(raw);
        assert_eq!(model["a"], "true");
        assert_eq!(model["b"], "false");
    }

    #[test]
    fn parse_negative_value() {
        let raw = "(model\n  (define-fun x () Real (- 1.0))\n)";
        let model = parse_model(raw);
        assert_eq!(model["x"], "-1.0");
    }

    #[test]
    fn parse_division() {
        let raw = "(model\n  (define-fun x () Real (/ 5.0 2.0))\n)";
        let model = parse_model(raw);
        assert_eq!(model["x"], "2.5");
    }

    #[test]
    fn parse_model_from_actual_z3_output() {
        let raw = r#"(
  (define-fun asserts_test_target_value_4 () Real
    (/ 5.0 2.0))
  (define-fun asserts_test_target_value_3 () Real
    5.0)
  (define-fun asserts_test_target_value_2 () Real
    10.0)
  (define-fun asserts_test_target_value_0 () Real
    40.0)
  (define-fun asserts_test_target_value_1 () Real
    20.0)
)"#;
        let model = parse_model(raw);
        assert_eq!(model.len(), 5);
        assert_eq!(model["asserts_test_target_value_0"], "40.0");
        assert_eq!(model["asserts_test_target_value_1"], "20.0");
        assert_eq!(model["asserts_test_target_value_2"], "10.0");
        assert_eq!(model["asserts_test_target_value_3"], "5.0");
        assert_eq!(model["asserts_test_target_value_4"], "2.5");
    }

    // -- Internal variable filter tests --

    #[test]
    fn is_internal_filters_run_vars() {
        assert!(is_internal("@__run_0"));
    }

    #[test]
    fn is_internal_filters_block_selectors() {
        assert!(is_internal("block1true_1"));
        assert!(is_internal("block2false_2"));
        assert!(!is_internal("blockchain_value_0"));
    }

    #[test]
    fn is_internal_passes_normal_vars() {
        assert!(!is_internal("cache_r_machine_blocks_0"));
        assert!(!is_internal("asserts_test_target_value_1"));
    }

    // -- SSA helper tests --

    #[test]
    fn split_ssa_works() {
        assert_eq!(split_ssa("foo_bar_3"), Some(("foo_bar", 3)));
        assert_eq!(split_ssa("x_0"), Some(("x", 0)));
        assert_eq!(split_ssa("noindex"), None);
    }

    #[test]
    fn strip_spec_prefix_works() {
        assert_eq!(strip_spec_prefix("asserts_test_value", "asserts"), "test_value");
        assert_eq!(strip_spec_prefix("other_test_value", "asserts"), "other_test_value");
    }

    // -- Event log replay tests --

    #[test]
    fn format_event_log_set_variable() {
        let mut log = EventLog::new("test");
        log.log_run_start(1);
        log.log_function_entry("test_r_fn", 1);
        log.log_variable_update("test_r_x_1");
        log.log_function_exit("test_r_fn");
        log.results.insert("test_r_x_1".into(), "42.0".into());

        let out = format_from_event_log(&log);
        assert!(out.contains("Start model, run for 1 rounds"));
        assert!(out.contains("Run function test_r_fn (round 1)"));
        assert!(out.contains("Set variable test_r_x to value 42.0"));
    }

    #[test]
    fn format_event_log_transition() {
        let mut log = EventLog::new("test");
        log.log_run_start(2);
        log.log_function_entry("test_fn", 1);
        log.log_variable_update("test_x_1");
        log.log_function_exit("test_fn");
        log.log_function_entry("test_fn", 2);
        log.log_variable_update("test_x_2");
        log.log_function_exit("test_fn");
        log.results.insert("test_x_1".into(), "10.0".into());
        log.results.insert("test_x_2".into(), "20.0".into());

        let out = format_from_event_log(&log);
        assert!(out.contains("Set variable test_x to value 10.0"));
        assert!(out.contains("test_x: 10.0 → 20.0"));
    }

    #[test]
    fn format_event_log_still() {
        let mut log = EventLog::new("test");
        log.log_run_start(2);
        log.log_function_entry("test_fn", 1);
        log.log_variable_update("test_x_1");
        log.log_function_exit("test_fn");
        log.log_function_entry("test_fn", 2);
        log.log_variable_update("test_x_2");
        log.log_function_exit("test_fn");
        log.results.insert("test_x_1".into(), "5.0".into());
        log.results.insert("test_x_2".into(), "5.0".into());

        let out = format_from_event_log(&log);
        assert!(out.contains("Set variable test_x to value 5.0"));
        assert!(out.contains("Variable test_x is still 5.0"));
    }

    #[test]
    fn format_event_log_filters_internal() {
        let mut log = EventLog::new("test");
        log.log_run_start(1);
        log.log_variable_update("@__run_0");
        log.log_variable_update("block1true_1");
        log.log_variable_update("test_x_1");
        log.results.insert("@__run_0".into(), "true".into());
        log.results.insert("block1true_1".into(), "true".into());
        log.results.insert("test_x_1".into(), "7.0".into());

        let out = format_from_event_log(&log);
        assert!(!out.contains("@__run"));
        assert!(!out.contains("block1true"));
        assert!(out.contains("test_x"));
    }

    #[test]
    fn format_event_log_indentation() {
        let mut log = EventLog::new("test");
        log.log_run_start(1);
        log.log_function_entry("test_outer", 1);
        log.log_function_entry("test_inner", 1);
        log.log_variable_update("test_x_1");
        log.log_function_exit("test_inner");
        log.log_function_exit("test_outer");
        log.results.insert("test_x_1".into(), "1.0".into());

        let out = format_from_event_log(&log);
        // The variable should be indented deeper than the inner function
        assert!(out.contains("   Run function test_outer"));
        assert!(out.contains("      Run function test_inner"));
        assert!(out.contains("         Set variable test_x"));
    }

    #[test]
    fn format_event_log_solvable() {
        let mut log = EventLog::new("test");
        log.log_run_start(1);
        log.log_solvable("test_a_0");
        log.results.insert("test_a_0".into(), "7.0".into());

        let out = format_from_event_log(&log);
        assert!(out.contains("Resolving variable test_a to value 7.0"));
    }

    // -- Flat fallback tests --

    #[test]
    fn format_flat_basic() {
        let mut model = BTreeMap::new();
        model.insert("spec_var_0".into(), "40.0".into());
        model.insert("spec_var_1".into(), "20.0".into());
        model.insert("spec_var_2".into(), "10.0".into());

        let out = format_counterexample_flat(&model, "spec");
        assert!(out.contains("COUNTEREXAMPLE FOUND"));
        assert!(out.contains("step 0: 40.0"));
        assert!(out.contains("40.0 → 20.0"));
    }

    #[test]
    fn format_flat_skips_unchanged() {
        let mut model = BTreeMap::new();
        model.insert("s_x_0".into(), "5.0".into());
        model.insert("s_x_1".into(), "5.0".into());
        model.insert("s_x_2".into(), "5.0".into());
        model.insert("s_x_3".into(), "10.0".into());

        let out = format_counterexample_flat(&model, "s");
        assert!(out.contains("step 0: 5.0"));
        assert!(!out.contains("step 1"));
        assert!(out.contains("step 3: 5.0 → 10.0"));
    }

    // -- Integration: format_counterexample dispatch --

    #[test]
    fn format_counterexample_uses_event_log_when_available() {
        let mut model = BTreeMap::new();
        model.insert("test_x_1".into(), "42.0".into());

        let mut log = EventLog::new("test");
        log.log_run_start(1);
        log.log_function_entry("test_fn", 1);
        log.log_variable_update("test_x_1");
        log.log_function_exit("test_fn");

        let out = format_counterexample(&model, &mut log);
        assert!(out.contains("Start model"));
        assert!(out.contains("Run function test_fn"));
        assert!(out.contains("Set variable test_x to value 42.0"));
    }

    #[test]
    fn format_counterexample_falls_back_to_flat() {
        let mut model = BTreeMap::new();
        model.insert("spec_var_0".into(), "1.0".into());
        model.insert("spec_var_1".into(), "2.0".into());

        let mut log = EventLog::new("spec");
        // Empty event log → flat fallback
        let out = format_counterexample(&model, &mut log);
        assert!(out.contains("COUNTEREXAMPLE FOUND"));
        assert!(out.contains("step 0: 1.0"));
    }
}
