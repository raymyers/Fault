//! State and expression evaluation for the Fault language.
//!
//! Mirrors `semantics/FaultSemantics/State.lean` (FaultState, SVal)
//! and `semantics/FaultSemantics/LTS.lean` (eval, evalBinOp, applyFlowOp).

use std::collections::HashMap;

use fault_resolve::ResolvedProgram;
use fault_syntax::*;

// ── Semantic values (State.lean:12) ─────────────────────────────────

/// Semantic values after evaluation.
/// All numerics become reals (f64) for SMT encoding (QF_NRA).
#[derive(Debug, Clone, PartialEq)]
pub enum SVal {
    Real(f64),
    Bool(bool),
    Nil,
}

impl SVal {
    pub fn is_nil(&self) -> bool {
        matches!(self, SVal::Nil)
    }
}

// ── Conversion (Val → SVal) ─────────────────────────────────────────

/// Convert a syntactic value to a semantic value.
/// - Numerics → Real
/// - Strings → Bool(false)  (Go compiler convention)
/// - Unknown/Uncertain → Nil (for deterministic evaluation)
pub fn to_sval(val: &Val) -> SVal {
    match val {
        Val::Nat(n) => SVal::Real(*n as f64),
        Val::Float(f) => SVal::Real(*f),
        Val::Bool(b) => SVal::Bool(*b),
        Val::Str(_) => SVal::Bool(false),
        Val::Unknown | Val::Uncertain { .. } | Val::Nil => SVal::Nil,
    }
}

// ── FaultState (State.lean:31) ──────────────────────────────────────

/// The complete state of a Fault model at a point in execution.
#[derive(Debug, Clone)]
pub struct FaultState {
    /// Stock property values (the store).
    pub env: HashMap<Name, SVal>,
    /// Current simulation round (0-indexed).
    pub round: u64,
    /// Component → current state name.
    pub comp_state: HashMap<Name, Name>,
    /// Variable history: (name, round) → value.
    pub history: HashMap<(Name, u64), SVal>,
}

impl FaultState {
    /// Read a variable from the environment. Returns Nil if not found.
    pub fn get_var(&self, name: &str) -> SVal {
        self.env.get(name).cloned().unwrap_or(SVal::Nil)
    }

    /// Set a variable in the environment.
    pub fn set_var(&mut self, name: String, val: SVal) {
        self.env.insert(name, val);
    }

    /// Update a component's current state.
    pub fn set_comp_state(&mut self, comp: String, state: String) {
        self.comp_state.insert(comp, state);
    }

    /// Snapshot current env into history at the current round.
    pub fn snapshot(&mut self, vars: &[Name]) {
        for var in vars {
            let val = self.get_var(var);
            self.history.insert((var.clone(), self.round), val);
        }
    }

    /// Advance to the next round.
    pub fn next_round(&mut self) {
        self.round += 1;
    }

    /// Read a historical value: x[now + offset] where offset is typically negative.
    pub fn read_history(&self, name: &str, offset: i64) -> SVal {
        let target = self.round as i64 + offset;
        if target >= 0 {
            self.history
                .get(&(name.to_string(), target as u64))
                .cloned()
                .unwrap_or(SVal::Nil)
        } else {
            SVal::Nil
        }
    }
}

// ── Initial state (State.lean:98) ───────────────────────────────────

/// Build the initial FaultState from a resolved program.
pub fn build_initial_state(prog: &ResolvedProgram) -> FaultState {
    let mut env = HashMap::new();

    // Initialize from stock properties
    for stock in &prog.stocks {
        for (name, val) in &stock.props {
            env.insert(name.clone(), to_sval(val));
        }
    }

    // Initialize from constants
    for c in &prog.constants {
        env.insert(c.name.clone(), to_sval(&c.value));
    }

    // Initialize component states
    let mut comp_state = HashMap::new();
    for (comp, state) in &prog.start_states {
        comp_state.insert(comp.clone(), state.clone());
    }

    FaultState {
        env,
        round: 0,
        comp_state,
        history: HashMap::new(),
    }
}

// ── Expression evaluation (LTS.lean:23) ─────────────────────────────

/// Deterministic expression evaluation against a state.
/// For unknown/uncertain values, returns Nil.
pub fn eval(state: &FaultState, expr: &Expr) -> SVal {
    match expr {
        Expr::Lit(val) => to_sval(val),
        Expr::Var(name) => state.get_var(name),
        Expr::BinOp { op, left, right } => {
            let l = eval(state, left);
            let r = eval(state, right);
            eval_binop(*op, l, r)
        }
        Expr::UnOp { op, expr } => {
            let v = eval(state, expr);
            eval_unop(*op, v)
        }
        Expr::Dot { expr, .. } => eval(state, expr), // should be resolved away
        Expr::History { name, offset } => state.read_history(name, *offset),
        Expr::Choose(_) => SVal::Nil, // nondeterministic: resolved at SMT level
    }
}

// ── Binary operations (LTS.lean:15) ─────────────────────────────────

/// Evaluate a binary operation on semantic values.
/// Nil propagation: any op with Nil → Nil (catch-all at bottom).
pub fn eval_binop(op: BinOp, l: SVal, r: SVal) -> SVal {
    match (op, &l, &r) {
        // Arithmetic on reals
        (BinOp::Add, SVal::Real(a), SVal::Real(b)) => SVal::Real(a + b),
        (BinOp::Sub, SVal::Real(a), SVal::Real(b)) => SVal::Real(a - b),
        (BinOp::Mul, SVal::Real(a), SVal::Real(b)) => SVal::Real(a * b),
        (BinOp::Div, SVal::Real(a), SVal::Real(b)) => SVal::Real(a / b),
        (BinOp::Mod, SVal::Real(a), SVal::Real(b)) => SVal::Real(a % b),
        (BinOp::Exp, SVal::Real(a), SVal::Real(b)) => SVal::Real(a.powf(*b)),

        // Comparisons on reals
        (BinOp::Eq, SVal::Real(a), SVal::Real(b)) => SVal::Bool(a == b),
        (BinOp::Neq, SVal::Real(a), SVal::Real(b)) => SVal::Bool(a != b),
        (BinOp::Lt, SVal::Real(a), SVal::Real(b)) => SVal::Bool(a < b),
        (BinOp::Le, SVal::Real(a), SVal::Real(b)) => SVal::Bool(a <= b),
        (BinOp::Gt, SVal::Real(a), SVal::Real(b)) => SVal::Bool(a > b),
        (BinOp::Ge, SVal::Real(a), SVal::Real(b)) => SVal::Bool(a >= b),

        // Boolean operations
        (BinOp::And, SVal::Bool(a), SVal::Bool(b)) => SVal::Bool(*a && *b),
        (BinOp::Or, SVal::Bool(a), SVal::Bool(b)) => SVal::Bool(*a || *b),

        // Equality on booleans
        (BinOp::Eq, SVal::Bool(a), SVal::Bool(b)) => SVal::Bool(a == b),
        (BinOp::Neq, SVal::Bool(a), SVal::Bool(b)) => SVal::Bool(a != b),

        // Nil propagation: any other combination → Nil
        _ => SVal::Nil,
    }
}

// ── Unary operations (LTS.lean:41) ──────────────────────────────────

/// Evaluate a unary operation.
pub fn eval_unop(op: UnOp, v: SVal) -> SVal {
    match (op, &v) {
        (UnOp::Neg, SVal::Real(a)) => SVal::Real(-a),
        (UnOp::Not, SVal::Bool(a)) => SVal::Bool(!a),
        _ => SVal::Nil,
    }
}

// ── Flow operators (LTS.lean:42→end) ────────────────────────────────

/// Apply a flow operation to a current value.
/// - Assign: replace current with new
/// - Inflow: current + new
/// - Outflow: current - new
pub fn apply_flow_op(op: FlowOp, current: SVal, new_val: SVal) -> SVal {
    match op {
        FlowOp::Assign => new_val,
        FlowOp::Inflow => match (&current, &new_val) {
            (SVal::Real(a), SVal::Real(b)) => SVal::Real(a + b),
            _ => new_val,
        },
        FlowOp::Outflow => match (&current, &new_val) {
            (SVal::Real(a), SVal::Real(b)) => SVal::Real(a - b),
            _ => new_val,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── to_sval tests ───────────────────────────────────────────────

    #[test]
    fn to_sval_conversions() {
        assert_eq!(to_sval(&Val::Nat(42)), SVal::Real(42.0));
        assert_eq!(to_sval(&Val::Float(3.14)), SVal::Real(3.14));
        assert_eq!(to_sval(&Val::Bool(true)), SVal::Bool(true));
        assert_eq!(to_sval(&Val::Str("hello".into())), SVal::Bool(false));
        assert_eq!(to_sval(&Val::Unknown), SVal::Nil);
        assert_eq!(
            to_sval(&Val::Uncertain {
                mean: 0.0,
                sigma: 1.0
            }),
            SVal::Nil
        );
        assert_eq!(to_sval(&Val::Nil), SVal::Nil);
    }

    // ── FaultState tests ────────────────────────────────────────────

    #[test]
    fn state_get_set_var() {
        let mut state = FaultState {
            env: HashMap::new(),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        assert_eq!(state.get_var("x"), SVal::Nil);
        state.set_var("x".into(), SVal::Real(10.0));
        assert_eq!(state.get_var("x"), SVal::Real(10.0));
    }

    #[test]
    fn state_history() {
        let mut state = FaultState {
            env: HashMap::new(),
            round: 2,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        state.history.insert(("x".into(), 0), SVal::Real(1.0));
        state.history.insert(("x".into(), 1), SVal::Real(2.0));

        // now=2, offset=-1 → round 1
        assert_eq!(state.read_history("x", -1), SVal::Real(2.0));
        // now=2, offset=-2 → round 0
        assert_eq!(state.read_history("x", -2), SVal::Real(1.0));
        // now=2, offset=-3 → round -1, negative → Nil
        assert_eq!(state.read_history("x", -3), SVal::Nil);
        // Nonexistent var
        assert_eq!(state.read_history("y", -1), SVal::Nil);
    }

    #[test]
    fn state_snapshot_and_advance() {
        let mut state = FaultState {
            env: HashMap::from([("x".into(), SVal::Real(5.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        state.snapshot(&["x".into()]);
        assert_eq!(state.history.get(&("x".into(), 0)), Some(&SVal::Real(5.0)));

        state.next_round();
        assert_eq!(state.round, 1);

        state.set_var("x".into(), SVal::Real(10.0));
        state.snapshot(&["x".into()]);
        assert_eq!(state.history.get(&("x".into(), 1)), Some(&SVal::Real(10.0)));
    }

    // ── build_initial_state tests ───────────────────────────────────

    #[test]
    fn build_initial_state_from_spec() {
        let prog = ResolvedProgram {
            stocks: vec![StockDef {
                name: "st".into(),
                props: vec![("value".into(), Val::Nat(30))],
            }],
            flows: vec![],
            constants: vec![ConstDef {
                name: "c".into(),
                value: Val::Bool(true),
                expr: None,
            }],
            components: vec![],
            invariants: vec![],
            start_states: vec![("drain".into(), "initial".into())],
            rounds: 1,
            init_block: vec![],
            run_block: vec![],
            var_names: vec!["value".into()],
        };

        let state = build_initial_state(&prog);
        assert_eq!(state.round, 0);
        assert_eq!(state.get_var("value"), SVal::Real(30.0));
        assert_eq!(state.get_var("c"), SVal::Bool(true));
        assert_eq!(state.get_var("nonexistent"), SVal::Nil);
        assert_eq!(state.comp_state.get("drain"), Some(&"initial".to_string()));
    }

    // ── eval tests ──────────────────────────────────────────────────

    fn empty_state() -> FaultState {
        FaultState {
            env: HashMap::new(),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        }
    }

    #[test]
    fn eval_literals() {
        let s = empty_state();
        assert_eq!(eval(&s, &Expr::Lit(Val::Nat(5))), SVal::Real(5.0));
        assert_eq!(eval(&s, &Expr::Lit(Val::Float(2.5))), SVal::Real(2.5));
        assert_eq!(eval(&s, &Expr::Lit(Val::Bool(true))), SVal::Bool(true));
        assert_eq!(
            eval(&s, &Expr::Lit(Val::Str("hi".into()))),
            SVal::Bool(false)
        );
        assert_eq!(eval(&s, &Expr::Lit(Val::Unknown)), SVal::Nil);
        assert_eq!(eval(&s, &Expr::Lit(Val::Nil)), SVal::Nil);
    }

    #[test]
    fn eval_var() {
        let mut s = empty_state();
        s.set_var("x".into(), SVal::Real(42.0));

        assert_eq!(eval(&s, &Expr::Var("x".into())), SVal::Real(42.0));
        assert_eq!(eval(&s, &Expr::Var("y".into())), SVal::Nil);
    }

    #[test]
    fn eval_arithmetic() {
        let s = empty_state();
        let make = |op, l: f64, r: f64| Expr::BinOp {
            op,
            left: Box::new(Expr::Lit(Val::Float(l))),
            right: Box::new(Expr::Lit(Val::Float(r))),
        };

        assert_eq!(eval(&s, &make(BinOp::Add, 3.0, 4.0)), SVal::Real(7.0));
        assert_eq!(eval(&s, &make(BinOp::Sub, 10.0, 3.0)), SVal::Real(7.0));
        assert_eq!(eval(&s, &make(BinOp::Mul, 3.0, 4.0)), SVal::Real(12.0));
        assert_eq!(eval(&s, &make(BinOp::Div, 10.0, 4.0)), SVal::Real(2.5));
        assert_eq!(eval(&s, &make(BinOp::Mod, 10.0, 3.0)), SVal::Real(1.0));
        assert_eq!(eval(&s, &make(BinOp::Exp, 2.0, 3.0)), SVal::Real(8.0));
    }

    #[test]
    fn eval_comparison() {
        let s = empty_state();
        let make = |op, l: f64, r: f64| Expr::BinOp {
            op,
            left: Box::new(Expr::Lit(Val::Float(l))),
            right: Box::new(Expr::Lit(Val::Float(r))),
        };

        assert_eq!(eval(&s, &make(BinOp::Eq, 3.0, 3.0)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::Eq, 3.0, 4.0)), SVal::Bool(false));
        assert_eq!(eval(&s, &make(BinOp::Neq, 3.0, 4.0)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::Lt, 3.0, 4.0)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::Lt, 4.0, 3.0)), SVal::Bool(false));
        assert_eq!(eval(&s, &make(BinOp::Le, 3.0, 3.0)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::Gt, 4.0, 3.0)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::Ge, 3.0, 3.0)), SVal::Bool(true));
    }

    #[test]
    fn eval_logical() {
        let s = empty_state();
        let make = |op, l: bool, r: bool| Expr::BinOp {
            op,
            left: Box::new(Expr::Lit(Val::Bool(l))),
            right: Box::new(Expr::Lit(Val::Bool(r))),
        };

        assert_eq!(eval(&s, &make(BinOp::And, true, true)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::And, true, false)), SVal::Bool(false));
        assert_eq!(eval(&s, &make(BinOp::Or, false, true)), SVal::Bool(true));
        assert_eq!(eval(&s, &make(BinOp::Or, false, false)), SVal::Bool(false));
    }

    #[test]
    fn eval_unary() {
        let s = empty_state();

        let neg_expr = Expr::UnOp {
            op: UnOp::Neg,
            expr: Box::new(Expr::Lit(Val::Float(5.0))),
        };
        assert_eq!(eval(&s, &neg_expr), SVal::Real(-5.0));

        let not_expr = Expr::UnOp {
            op: UnOp::Not,
            expr: Box::new(Expr::Lit(Val::Bool(true))),
        };
        assert_eq!(eval(&s, &not_expr), SVal::Bool(false));
    }

    #[test]
    fn eval_nil_propagation() {
        let s = empty_state();

        // Unknown + 5 → Nil
        let expr = Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Lit(Val::Unknown)),
            right: Box::new(Expr::Lit(Val::Nat(5))),
        };
        assert_eq!(eval(&s, &expr), SVal::Nil);

        // 5 + Unknown → Nil
        let expr2 = Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Lit(Val::Nat(5))),
            right: Box::new(Expr::Lit(Val::Unknown)),
        };
        assert_eq!(eval(&s, &expr2), SVal::Nil);

        // !Nil → Nil
        let expr3 = Expr::UnOp {
            op: UnOp::Not,
            expr: Box::new(Expr::Lit(Val::Nil)),
        };
        assert_eq!(eval(&s, &expr3), SVal::Nil);
    }

    #[test]
    fn eval_choose_returns_nil() {
        let s = empty_state();
        let expr = Expr::Choose(vec![Expr::Lit(Val::Nat(1)), Expr::Lit(Val::Nat(2))]);
        // Deterministic eval returns Nil for Choose (nondeterministic)
        assert_eq!(eval(&s, &expr), SVal::Nil);
    }

    #[test]
    fn eval_history_ref() {
        let mut s = empty_state();
        s.history.insert(("x".into(), 0), SVal::Real(100.0));
        s.round = 1;

        let expr = Expr::History {
            name: "x".into(),
            offset: -1,
        };
        assert_eq!(eval(&s, &expr), SVal::Real(100.0));
    }

    // ── Flow operator tests ─────────────────────────────────────────

    #[test]
    fn flow_assign() {
        assert_eq!(
            apply_flow_op(FlowOp::Assign, SVal::Real(10.0), SVal::Real(5.0)),
            SVal::Real(5.0)
        );
    }

    #[test]
    fn flow_inflow() {
        assert_eq!(
            apply_flow_op(FlowOp::Inflow, SVal::Real(10.0), SVal::Real(5.0)),
            SVal::Real(15.0)
        );
    }

    #[test]
    fn flow_outflow() {
        assert_eq!(
            apply_flow_op(FlowOp::Outflow, SVal::Real(10.0), SVal::Real(5.0)),
            SVal::Real(5.0)
        );
    }

    #[test]
    fn flow_op_with_nil() {
        // Inflow with Nil current → just use new value
        assert_eq!(
            apply_flow_op(FlowOp::Inflow, SVal::Nil, SVal::Real(5.0)),
            SVal::Real(5.0)
        );
    }

    // ── Compound expression test ────────────────────────────────────

    #[test]
    fn eval_nested_expression() {
        // (x + 2) > 4 where x = 3 → true
        let mut s = empty_state();
        s.set_var("x".into(), SVal::Real(3.0));

        let expr = Expr::BinOp {
            op: BinOp::Gt,
            left: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(2))),
            }),
            right: Box::new(Expr::Lit(Val::Nat(4))),
        };
        assert_eq!(eval(&s, &expr), SVal::Bool(true));
    }

    #[test]
    fn eval_boolean_eq_neq() {
        let s = empty_state();
        assert_eq!(
            eval_binop(BinOp::Eq, SVal::Bool(true), SVal::Bool(true)),
            SVal::Bool(true)
        );
        assert_eq!(
            eval_binop(BinOp::Eq, SVal::Bool(true), SVal::Bool(false)),
            SVal::Bool(false)
        );
        assert_eq!(
            eval_binop(BinOp::Neq, SVal::Bool(true), SVal::Bool(false)),
            SVal::Bool(true)
        );
        let _ = s; // suppress unused
    }
}
