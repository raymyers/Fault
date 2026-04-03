//! Parse Z3 model output into structured variable maps and format
//! human-readable counterexample traces.

use std::collections::BTreeMap;

/// Parse Z3 `(model (define-fun …) …)` output into name → value pairs.
///
/// Handles values that are:
/// - Simple literals: `40.0`, `true`, `7.0`
/// - Negative: `(- 1.0)` → `-1.0`
/// - S-expressions: `(/ 5.0 2.0)` → `2.5`
pub fn parse_model(raw: &str) -> BTreeMap<String, String> {
    let mut result = BTreeMap::new();
    let mut chars = raw.chars().peekable();

    while let Some(&ch) = chars.peek() {
        if ch == '(' {
            // Try to match "(define-fun"
            let rest: String = chars.clone().take(11).collect();
            if rest == "(define-fun" {
                // Consume "(define-fun"
                for _ in 0..11 {
                    chars.next();
                }
                skip_ws(&mut chars);
                let name = read_symbol(&mut chars);
                skip_ws(&mut chars);
                // Skip "()" — the empty arg list
                expect_char(&mut chars, '(');
                expect_char(&mut chars, ')');
                skip_ws(&mut chars);
                // Skip type (Real, Bool, Int, etc.)
                let _type = read_symbol(&mut chars);
                skip_ws(&mut chars);
                // Read value (may be an S-expression)
                let value_raw = read_value(&mut chars);
                skip_ws(&mut chars);
                // Closing paren of define-fun
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

/// Identify internal solver variables that should be hidden from the user.
fn is_internal(name: &str) -> bool {
    if name.starts_with("@__run") {
        return true;
    }
    // block selectors: block<N>true_<N>, block<N>false_<N>
    if name
        .strip_prefix("block")
        .is_some_and(|rest| rest.contains("true") || rest.contains("false"))
    {
        return true;
    }
    // state selectors
    if name.contains("__state-%") {
        return true;
    }
    false
}

/// Split an SSA variable name like "spec_inst_prop_3" into (base, ssa_index).
/// Returns None if the name doesn't end with `_<digits>`.
fn split_ssa(name: &str) -> Option<(&str, u32)> {
    let idx = name.rfind('_')?;
    let suffix = &name[idx + 1..];
    let n: u32 = suffix.parse().ok()?;
    Some((&name[..idx], n))
}

/// Strip the spec-name prefix from a variable name.
/// E.g., "asserts_test_target_value" with spec "asserts" → "test_target_value".
fn strip_spec_prefix<'a>(name: &'a str, spec_name: &str) -> &'a str {
    let prefix = format!("{}_", spec_name);
    name.strip_prefix(&prefix).unwrap_or(name)
}

/// Format a counterexample model as a human-readable string.
///
/// Groups SSA variables by base name, orders by step, and shows transitions.
pub fn format_counterexample(model: &BTreeMap<String, String>, spec_name: &str) -> String {
    let mut out = String::from("COUNTEREXAMPLE FOUND\n");
    out.push_str("The following assertion can be violated:\n\n");

    // Group: display_base → sorted vec of (ssa_index, value)
    let mut groups: BTreeMap<String, Vec<(u32, String)>> = BTreeMap::new();
    // Variables without SSA suffix (constants)
    let mut constants: BTreeMap<String, String> = BTreeMap::new();

    for (name, value) in model {
        if is_internal(name) {
            continue;
        }
        let display_name = strip_spec_prefix(name, spec_name);

        if let Some((base, idx)) = split_ssa(display_name) {
            groups
                .entry(base.to_string())
                .or_default()
                .push((idx, value.clone()));
        } else {
            constants.insert(display_name.to_string(), value.clone());
        }
    }

    // Print constants first
    for (name, value) in &constants {
        out.push_str(&format!("  {} = {}\n", name, value));
    }
    if !constants.is_empty() {
        out.push('\n');
    }

    // Print variable timelines
    for (base, mut steps) in groups {
        steps.sort_by_key(|(idx, _)| *idx);

        out.push_str(&format!("  {}\n", base));
        let mut prev: Option<&str> = None;
        for (idx, val) in &steps {
            match prev {
                Some(p) if p == val => {
                    // Skip unchanged
                }
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

// ── Helpers ──────────────────────────────────────────────────────────────

fn skip_ws(chars: &mut std::iter::Peekable<std::str::Chars>) {
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
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

/// Read a value which may be a simple token or a parenthesized S-expression.
fn read_value(chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
    skip_ws(chars);
    if chars.peek() == Some(&'(') {
        read_sexpr(chars)
    } else {
        read_symbol(chars)
    }
}

/// Read a balanced parenthesized expression.
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
    // Simple literal
    if !s.starts_with('(') {
        return s.to_string();
    }

    // Try to evaluate simple arithmetic S-expressions
    let inner = &s[1..s.len() - 1].trim();
    let parts: Vec<&str> = inner.split_whitespace().collect();

    match parts.as_slice() {
        // Unary minus: (- 1.0) → -1.0
        ["-", val] => {
            if let Ok(v) = val.parse::<f64>() {
                format_float(-v)
            } else {
                format!("-{}", val)
            }
        }
        // Division: (/ 5.0 2.0) → 2.5
        ["/", a, b] => {
            if let (Ok(va), Ok(vb)) = (a.parse::<f64>(), b.parse::<f64>()) {
                if vb != 0.0 {
                    format_float(va / vb)
                } else {
                    s.to_string()
                }
            } else {
                s.to_string()
            }
        }
        // Multiplication: (* 3.0 2.0) → 6.0
        ["*", a, b] => {
            if let (Ok(va), Ok(vb)) = (a.parse::<f64>(), b.parse::<f64>()) {
                format_float(va * vb)
            } else {
                s.to_string()
            }
        }
        // Addition: (+ 3.0 2.0) → 5.0
        ["+", a, b] => {
            if let (Ok(va), Ok(vb)) = (a.parse::<f64>(), b.parse::<f64>()) {
                format_float(va + vb)
            } else {
                s.to_string()
            }
        }
        // Subtraction: (- 5.0 2.0) → 3.0
        ["-", a, b] => {
            if let (Ok(va), Ok(vb)) = (a.parse::<f64>(), b.parse::<f64>()) {
                format_float(va - vb)
            } else {
                s.to_string()
            }
        }
        _ => s.to_string(),
    }
}

/// Format a float, stripping unnecessary trailing zeros but keeping at least one decimal.
fn format_float(v: f64) -> String {
    if v == v.trunc() {
        format!("{:.1}", v)
    } else {
        // Remove trailing zeros
        let s = format!("{}", v);
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let raw = r#"(model
  (define-fun x () Real (- 1.0))
)"#;
        let model = parse_model(raw);
        assert_eq!(model["x"], "-1.0");
    }

    #[test]
    fn parse_division() {
        let raw = r#"(model
  (define-fun x () Real (/ 5.0 2.0))
)"#;
        let model = parse_model(raw);
        assert_eq!(model["x"], "2.5");
    }

    #[test]
    fn parse_integer_values() {
        let raw = r#"(model
  (define-fun x () Real 7.0)
  (define-fun y () Real 0.0)
)"#;
        let model = parse_model(raw);
        assert_eq!(model["x"], "7.0");
        assert_eq!(model["y"], "0.0");
    }

    #[test]
    fn is_internal_filters_run_vars() {
        assert!(is_internal("@__run_0"));
        assert!(is_internal("@__run_1"));
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

    #[test]
    fn format_counterexample_basic() {
        let mut model = BTreeMap::new();
        model.insert("spec_var_0".into(), "40.0".into());
        model.insert("spec_var_1".into(), "20.0".into());
        model.insert("spec_var_2".into(), "10.0".into());

        let out = format_counterexample(&model, "spec");
        assert!(out.contains("COUNTEREXAMPLE FOUND"));
        assert!(out.contains("var"));
        assert!(out.contains("step 0: 40.0"));
        assert!(out.contains("40.0 → 20.0"));
        assert!(out.contains("20.0 → 10.0"));
    }

    #[test]
    fn format_counterexample_filters_internal() {
        let mut model = BTreeMap::new();
        model.insert("spec_var_0".into(), "1.0".into());
        model.insert("@__run_0".into(), "true".into());
        model.insert("block1true_1".into(), "true".into());

        let out = format_counterexample(&model, "spec");
        assert!(out.contains("var"));
        assert!(!out.contains("@__run"));
        assert!(!out.contains("block1true"));
    }

    #[test]
    fn format_counterexample_skips_unchanged() {
        let mut model = BTreeMap::new();
        model.insert("s_x_0".into(), "5.0".into());
        model.insert("s_x_1".into(), "5.0".into());
        model.insert("s_x_2".into(), "5.0".into());
        model.insert("s_x_3".into(), "10.0".into());

        let out = format_counterexample(&model, "s");
        // Should show step 0 and step 3 (transition), but not steps 1 and 2
        assert!(out.contains("step 0: 5.0"));
        assert!(!out.contains("step 1"));
        assert!(!out.contains("step 2"));
        assert!(out.contains("step 3: 5.0 → 10.0"));
    }

    #[test]
    fn format_counterexample_booleans() {
        let mut model = BTreeMap::new();
        model.insert("test_flag_0".into(), "true".into());
        model.insert("test_flag_1".into(), "false".into());

        let out = format_counterexample(&model, "test");
        assert!(out.contains("flag"));
        assert!(out.contains("step 0: true"));
        assert!(out.contains("true → false"));
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

    #[test]
    fn format_full_asserts_example() {
        let mut model = BTreeMap::new();
        model.insert("asserts_test_target_value_0".into(), "40.0".into());
        model.insert("asserts_test_target_value_1".into(), "20.0".into());
        model.insert("asserts_test_target_value_2".into(), "10.0".into());
        model.insert("asserts_test_target_value_3".into(), "5.0".into());
        model.insert("asserts_test_target_value_4".into(), "2.5".into());

        let out = format_counterexample(&model, "asserts");
        assert!(out.contains("test_target_value"), "should strip spec prefix");
        assert!(out.contains("step 0: 40.0"), "should show initial");
        assert!(out.contains("40.0 → 20.0"), "should show transition");
        assert!(out.contains("20.0 → 10.0"));
        assert!(out.contains("10.0 → 5.0"));
        assert!(out.contains("5.0 → 2.5"));
    }
}
