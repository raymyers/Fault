//! Temporal logic and assertion checking for the Fault language.
//!
//! Mirrors `semantics/FaultSemantics/Temporal.lean`:
//! - Bounded temporal operators: always, eventually, eventually-always, nmt, nft
//! - Expression predicates over state traces
//! - Assertion/assumption checking
//! - Model checking query structure

use fault_eval::*;
use fault_syntax::*;

// ── Bounded temporal operators (Temporal.lean:17-40) ────────────────

/// `always` — P holds at every state in the trace.
pub fn check_always(states: &[FaultState], pred: &dyn Fn(&FaultState) -> bool) -> bool {
    states.iter().all(pred)
}

/// `eventually` — P holds at some state in the trace.
pub fn check_eventually(states: &[FaultState], pred: &dyn Fn(&FaultState) -> bool) -> bool {
    states.iter().any(pred)
}

/// `eventually-always` — there exists a point k after which P always holds.
pub fn check_eventually_always(states: &[FaultState], pred: &dyn Fn(&FaultState) -> bool) -> bool {
    for k in 0..states.len() {
        if states[k..].iter().all(pred) {
            return true;
        }
    }
    false
}

/// `nmt n` — P holds at most n times.
pub fn check_nmt(states: &[FaultState], pred: &dyn Fn(&FaultState) -> bool, n: u64) -> bool {
    let count = states.iter().filter(|s| pred(s)).count() as u64;
    count <= n
}

/// `nft n` — P holds at least n times.
pub fn check_nft(states: &[FaultState], pred: &dyn Fn(&FaultState) -> bool, n: u64) -> bool {
    let count = states.iter().filter(|s| pred(s)).count() as u64;
    count >= n
}

// ── Temporal interpretation (Temporal.lean:43) ──────────────────────

/// Interpret a temporal operator over a trace with a predicate.
pub fn interpret_temporal(
    temp: &Temporal,
    states: &[FaultState],
    pred: &dyn Fn(&FaultState) -> bool,
) -> bool {
    match temp {
        Temporal::Always => check_always(states, pred),
        Temporal::Eventually => check_eventually(states, pred),
        Temporal::EventuallyAlways => check_eventually_always(states, pred),
        Temporal::Nmt(n) => check_nmt(states, pred, *n),
        Temporal::Nft(n) => check_nft(states, pred, *n),
    }
}

// ── Expression predicates (Temporal.lean:51) ────────────────────────

/// Convert a Fault expression to a state predicate.
/// Returns true when the expression evaluates to Bool(true).
pub fn expr_predicate(expr: &Expr, state: &FaultState) -> bool {
    eval(state, expr) == SVal::Bool(true)
}

// ── Assertion/assumption checking (Temporal.lean:56-81) ─────────────

/// Check result for an invariant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    /// The invariant holds over the trace.
    Holds,
    /// The invariant is violated.
    Violated,
}

/// Check an invariant against a trace of states.
pub fn check_invariant(inv: &Invariant, states: &[FaultState]) -> CheckResult {
    let holds = match inv {
        Invariant::Assert { expr, temporal } => {
            let pred = |s: &FaultState| expr_predicate(expr, s);
            interpret_temporal(temporal, states, &pred)
        }
        Invariant::Assume { expr, temporal } => {
            let pred = |s: &FaultState| expr_predicate(expr, s);
            interpret_temporal(temporal, states, &pred)
        }
        Invariant::AssertWhen {
            guard,
            body,
            temporal,
        } => {
            let pred = |s: &FaultState| {
                if expr_predicate(guard, s) {
                    expr_predicate(body, s)
                } else {
                    true // guard not met → vacuously true
                }
            };
            interpret_temporal(temporal, states, &pred)
        }
        Invariant::AssumeWhen {
            guard,
            body,
            temporal,
        } => {
            let pred = |s: &FaultState| {
                if expr_predicate(guard, s) {
                    expr_predicate(body, s)
                } else {
                    true
                }
            };
            interpret_temporal(temporal, states, &pred)
        }
    };

    if holds {
        CheckResult::Holds
    } else {
        CheckResult::Violated
    }
}

/// Check all invariants against a trace.
pub fn check_all_invariants(invs: &[Invariant], states: &[FaultState]) -> Vec<CheckResult> {
    invs.iter()
        .map(|inv| check_invariant(inv, states))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn state_with_val(name: &str, val: f64) -> FaultState {
        FaultState {
            env: HashMap::from([(name.to_string(), SVal::Real(val))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        }
    }

    fn trace_of_values(name: &str, values: &[f64]) -> Vec<FaultState> {
        values.iter().map(|v| state_with_val(name, *v)).collect()
    }

    // ── Temporal operator tests ─────────────────────────────────────

    #[test]
    fn always_all_true() {
        let states = trace_of_values("x", &[1.0, 2.0, 3.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 0.0);
        assert!(check_always(&states, &pred));
    }

    #[test]
    fn always_one_false() {
        let states = trace_of_values("x", &[1.0, -1.0, 3.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 0.0);
        assert!(!check_always(&states, &pred));
    }

    #[test]
    fn eventually_found() {
        let states = trace_of_values("x", &[0.0, 0.0, 5.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 3.0);
        assert!(check_eventually(&states, &pred));
    }

    #[test]
    fn eventually_not_found() {
        let states = trace_of_values("x", &[0.0, 1.0, 2.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 10.0);
        assert!(!check_eventually(&states, &pred));
    }

    #[test]
    fn eventually_always_suffix() {
        // From index 2 onwards, all > 3
        let states = trace_of_values("x", &[0.0, 1.0, 5.0, 6.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 3.0);
        assert!(check_eventually_always(&states, &pred));
    }

    #[test]
    fn eventually_always_fails() {
        // No suffix where all > 3
        let states = trace_of_values("x", &[5.0, 1.0, 5.0, 1.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 3.0);
        assert!(!check_eventually_always(&states, &pred));
    }

    #[test]
    fn nmt_within_limit() {
        let states = trace_of_values("x", &[5.0, 1.0, 5.0, 1.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 3.0);
        assert!(check_nmt(&states, &pred, 2)); // exactly 2 times
        assert!(check_nmt(&states, &pred, 3)); // at most 3
        assert!(!check_nmt(&states, &pred, 1)); // more than 1
    }

    #[test]
    fn nft_meets_minimum() {
        let states = trace_of_values("x", &[5.0, 1.0, 5.0, 1.0]);
        let pred = |s: &FaultState| matches!(s.get_var("x"), SVal::Real(v) if v > 3.0);
        assert!(check_nft(&states, &pred, 2)); // exactly 2
        assert!(check_nft(&states, &pred, 1)); // at least 1
        assert!(!check_nft(&states, &pred, 3)); // fewer than 3
    }

    // ── Invariant checking tests ────────────────────────────────────

    #[test]
    fn assert_holds() {
        let states = trace_of_values("x", &[10.0, 20.0, 30.0]);

        let inv = Invariant::Assert {
            expr: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(0))),
            },
            temporal: Temporal::Always,
        };

        assert_eq!(check_invariant(&inv, &states), CheckResult::Holds);
    }

    #[test]
    fn assert_violated() {
        let states = trace_of_values("x", &[10.0, -5.0, 30.0]);

        let inv = Invariant::Assert {
            expr: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(0))),
            },
            temporal: Temporal::Always,
        };

        assert_eq!(check_invariant(&inv, &states), CheckResult::Violated);
    }

    #[test]
    fn assert_eventually() {
        let states = trace_of_values("x", &[0.0, 0.0, 5.0]);

        let inv = Invariant::Assert {
            expr: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(3))),
            },
            temporal: Temporal::Eventually,
        };

        assert_eq!(check_invariant(&inv, &states), CheckResult::Holds);
    }

    #[test]
    fn assert_when_then() {
        let states = trace_of_values("x", &[10.0, 20.0]);

        // assert when x > 5 then x > 8
        let inv = Invariant::AssertWhen {
            guard: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(5))),
            },
            body: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(8))),
            },
            temporal: Temporal::Always,
        };

        assert_eq!(check_invariant(&inv, &states), CheckResult::Holds);
    }

    #[test]
    fn assert_when_then_violated() {
        let states = trace_of_values("x", &[10.0, 7.0]);

        // assert when x > 5 then x > 8 — violated at x=7
        let inv = Invariant::AssertWhen {
            guard: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(5))),
            },
            body: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(8))),
            },
            temporal: Temporal::Always,
        };

        assert_eq!(check_invariant(&inv, &states), CheckResult::Violated);
    }

    #[test]
    fn check_all_mixed() {
        let states = trace_of_values("x", &[10.0, 20.0]);

        let results = check_all_invariants(
            &[
                Invariant::Assert {
                    expr: Expr::BinOp {
                        op: BinOp::Gt,
                        left: Box::new(Expr::Var("x".into())),
                        right: Box::new(Expr::Lit(Val::Nat(5))),
                    },
                    temporal: Temporal::Always,
                },
                Invariant::Assume {
                    expr: Expr::BinOp {
                        op: BinOp::Lt,
                        left: Box::new(Expr::Var("x".into())),
                        right: Box::new(Expr::Lit(Val::Nat(100))),
                    },
                    temporal: Temporal::Always,
                },
            ],
            &states,
        );

        assert_eq!(results, vec![CheckResult::Holds, CheckResult::Holds]);
    }

    #[test]
    fn empty_trace() {
        let states: Vec<FaultState> = vec![];

        // always on empty trace is vacuously true
        assert!(check_always(&states, &|_| false));
        // eventually on empty trace is false
        assert!(!check_eventually(&states, &|_| true));
    }
}
