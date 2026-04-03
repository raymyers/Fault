//! Statement and program execution for the Fault language.
//!
//! Mirrors `semantics/FaultSemantics/Execution.lean`:
//! - Single statement execution (ExecStmt)
//! - Sequential block execution (ExecStmts)
//! - Round execution with history snapshots
//! - Full program execution (init + N rounds)
//! - System execution with component state machines

use std::collections::HashMap;

use fault_eval::*;
use fault_resolve::ResolvedProgram;
use fault_syntax::*;

// ── Flow function lookup ────────────────────────────────────────────

/// Map from (flow_type_name, func_name) → function body.
pub type FlowFuncMap = HashMap<(String, String), Vec<Stmt>>;

/// Map from instance_name → flow_type_name (built during init).
pub type InstanceMap = HashMap<String, String>;

/// Build the flow function map from flow definitions.
pub fn build_flow_func_map(flows: &[FlowDef]) -> FlowFuncMap {
    let mut map = FlowFuncMap::new();
    for flow in flows {
        for (func_name, body) in &flow.funcs {
            map.insert((flow.name.clone(), func_name.clone()), body.clone());
        }
    }
    map
}

/// Resolve a Call name like "drawn.in" → find function body.
/// Splits on '.', looks up instance → flow type, then flow.func.
fn resolve_call<'a>(
    call_name: &str,
    instances: &InstanceMap,
    func_map: &'a FlowFuncMap,
) -> Option<&'a Vec<Stmt>> {
    if let Some(dot_pos) = call_name.rfind('.') {
        let instance = &call_name[..dot_pos];
        let func_name = &call_name[dot_pos + 1..];

        if let Some(flow_type) = instances.get(instance) {
            return func_map.get(&(flow_type.clone(), func_name.to_string()));
        }
    }
    None
}

// ── Statement execution (Execution.lean:23) ─────────────────────────

/// Execute a single statement, mutating the state.
/// Returns labels emitted during execution.
pub fn exec_stmt(
    state: &mut FaultState,
    stmt: &Stmt,
    instances: &InstanceMap,
    func_map: &FlowFuncMap,
) -> Vec<String> {
    let mut labels = Vec::new();

    match stmt {
        Stmt::FlowAssign { name, op, expr } => {
            let val = eval(state, expr);
            let current = state.get_var(name);
            let new_val = apply_flow_op(*op, current, val);
            state.set_var(name.clone(), new_val);
            labels.push(format!("assign:{}", name));
        }
        Stmt::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_val = eval(state, cond);
            match cond_val {
                SVal::Bool(true) => {
                    labels.push("branch:true".into());
                    labels.extend(exec_stmts(state, then_branch, instances, func_map));
                }
                SVal::Bool(false) => {
                    labels.push("branch:false".into());
                    labels.extend(exec_stmts(state, else_branch, instances, func_map));
                }
                _ => {
                    // Nil condition: skip (no branch taken)
                    labels.push("branch:nil".into());
                }
            }
        }
        Stmt::Call(name) => {
            if let Some(body) = resolve_call(name, instances, func_map) {
                let body = body.clone();
                labels.push(format!("call:{}", name));
                labels.extend(exec_stmts(state, &body, instances, func_map));
            }
        }
        Stmt::Advance(target) => {
            // Parse "this.state_name" format or bare name
            // For now, treat as setting comp state
            labels.push(format!("advance:{}", target));
            // Component state updates handled at system level
        }
        Stmt::Stay => {
            labels.push("stay".into());
        }
        Stmt::Seq(stmts) => {
            labels.extend(exec_stmts(state, stmts, instances, func_map));
        }
        Stmt::Parallel(stmts) => {
            // Canonical order: execute sequentially in declaration order
            labels.extend(exec_stmts(state, stmts, instances, func_map));
        }
        Stmt::CompoundTransition(_) | Stmt::ChooseTransition(_) => {
            labels.push("compound_transition".into());
        }
    }

    labels
}

/// Execute a list of statements sequentially.
pub fn exec_stmts(
    state: &mut FaultState,
    stmts: &[Stmt],
    instances: &InstanceMap,
    func_map: &FlowFuncMap,
) -> Vec<String> {
    let mut labels = Vec::new();
    for stmt in stmts {
        labels.extend(exec_stmt(state, stmt, instances, func_map));
    }
    labels
}

// ── Init block execution ────────────────────────────────────────────

/// Process the init block: create instances and apply swaps.
/// Returns the instance map (instance_name → flow_type_name).
pub fn exec_init_block(
    state: &mut FaultState,
    init_block: &[Stmt],
    instances: &mut InstanceMap,
    func_map: &FlowFuncMap,
) {
    for stmt in init_block {
        match stmt {
            Stmt::FlowAssign { name, expr, .. } => {
                if let Expr::Var(type_ref) = expr
                    && let Some(type_name) = type_ref.strip_prefix("new ")
                {
                    instances.insert(name.clone(), type_name.to_string());
                    continue;
                }
                // Swap or assignment: evaluate and set
                let val = eval(state, expr);
                state.set_var(name.clone(), val);
            }
            other => {
                exec_stmt(state, other, instances, func_map);
            }
        }
    }
}

// ── Round execution (Execution.lean:120) ────────────────────────────

/// Execute one round: run block → snapshot → next round.
pub fn exec_round(
    state: &mut FaultState,
    run_block: &[Stmt],
    var_names: &[Name],
    instances: &InstanceMap,
    func_map: &FlowFuncMap,
) -> Vec<String> {
    let mut labels = exec_stmts(state, run_block, instances, func_map);
    labels.push(format!("round:{}", state.round));
    state.snapshot(var_names);
    state.next_round();
    labels
}

/// Execute N rounds.
pub fn exec_rounds(
    state: &mut FaultState,
    n: u64,
    run_block: &[Stmt],
    var_names: &[Name],
    instances: &InstanceMap,
    func_map: &FlowFuncMap,
) -> Vec<String> {
    let mut labels = Vec::new();
    for _ in 0..n {
        labels.extend(exec_round(state, run_block, var_names, instances, func_map));
    }
    labels
}

// ── System execution with components (Execution.lean:150+) ──────────

/// Execute component state functions for all active components.
pub fn exec_components(
    state: &mut FaultState,
    components: &[CompDef],
    instances: &InstanceMap,
    func_map: &FlowFuncMap,
) -> Vec<String> {
    let mut labels = Vec::new();
    for comp in components {
        let current_state = state
            .comp_state
            .get(&comp.name)
            .cloned()
            .unwrap_or_default();

        if let Some((_, body)) = comp.states.iter().find(|(n, _)| *n == current_state) {
            let body = body.clone();
            labels.extend(exec_stmts(state, &body, instances, func_map));
        }
    }
    labels
}

/// Execute one system round: run block + components + snapshot.
pub fn exec_system_round(
    state: &mut FaultState,
    run_block: &[Stmt],
    components: &[CompDef],
    var_names: &[Name],
    instances: &InstanceMap,
    func_map: &FlowFuncMap,
) -> Vec<String> {
    let mut labels = exec_stmts(state, run_block, instances, func_map);
    labels.extend(exec_components(state, components, instances, func_map));
    labels.push(format!("round:{}", state.round));
    state.snapshot(var_names);
    state.next_round();
    labels
}

// ── Full program execution (Execution.lean:173) ─────────────────────

/// Execute a complete spec program: init once, then N rounds.
pub fn exec_program(prog: &ResolvedProgram) -> (FaultState, Vec<String>) {
    let mut state = build_initial_state(prog);
    let func_map = build_flow_func_map(&prog.flows);
    let mut instances = InstanceMap::new();

    // Init block
    exec_init_block(&mut state, &prog.init_block, &mut instances, &func_map);

    // N rounds
    let labels = exec_rounds(
        &mut state,
        prog.rounds,
        &prog.run_block,
        &prog.var_names,
        &instances,
        &func_map,
    );

    (state, labels)
}

/// Execute a complete system program: init once, then N rounds with components.
pub fn exec_system_program(prog: &ResolvedProgram) -> (FaultState, Vec<String>) {
    let mut state = build_initial_state(prog);
    let func_map = build_flow_func_map(&prog.flows);
    let mut instances = InstanceMap::new();

    // Init block
    exec_init_block(&mut state, &prog.init_block, &mut instances, &func_map);

    // N system rounds
    let mut labels = Vec::new();
    for _ in 0..prog.rounds {
        labels.extend(exec_system_round(
            &mut state,
            &prog.run_block,
            &prog.components,
            &prog.var_names,
            &instances,
            &func_map,
        ));
    }

    (state, labels)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_simple_spec_program() -> ResolvedProgram {
        // Simulates: stock value=30; flow fn: if value > 4 { value <- value - 2 }
        // for 1 init{l = new fl;} run { l.fn; }
        ResolvedProgram {
            stocks: vec![StockDef {
                name: "st".into(),
                props: vec![("value".into(), Val::Nat(30))],
            }],
            flows: vec![FlowDef {
                name: "fl".into(),
                stocks: vec![("vault".into(), "st".into())],
                funcs: vec![(
                    "fn".into(),
                    vec![Stmt::IfThenElse {
                        cond: Expr::BinOp {
                            op: BinOp::Gt,
                            left: Box::new(Expr::Var("value".into())),
                            right: Box::new(Expr::Lit(Val::Nat(4))),
                        },
                        then_branch: vec![Stmt::FlowAssign {
                            name: "value".into(),
                            op: FlowOp::Inflow,
                            expr: Expr::BinOp {
                                op: BinOp::Sub,
                                left: Box::new(Expr::Var("value".into())),
                                right: Box::new(Expr::Lit(Val::Nat(2))),
                            },
                        }],
                        else_branch: vec![],
                    }],
                )],
            }],
            constants: vec![],
            components: vec![],
            invariants: vec![],
            start_states: vec![],
            rounds: 1,
            init_block: vec![Stmt::FlowAssign {
                name: "l".into(),
                op: FlowOp::Assign,
                expr: Expr::Var("new fl".into()),
            }],
            run_block: vec![Stmt::Call("l.fn".into())],
            var_names: vec!["value".into()],
            imported_constants: vec![],
            import_alias_map: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn exec_simple_one_round() {
        let prog = make_simple_spec_program();
        let (state, labels) = exec_program(&prog);

        // value started at 30, fn does: value <- value - 2 (inflow of value-2=28)
        // value = 30 + 28 = 58
        assert_eq!(state.get_var("value"), SVal::Real(58.0));
        assert!(!labels.is_empty());
    }

    #[test]
    fn exec_flow_assign_direct() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("x".into(), SVal::Real(10.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        let stmt = Stmt::FlowAssign {
            name: "x".into(),
            op: FlowOp::Assign,
            expr: Expr::Lit(Val::Nat(5)),
        };
        exec_stmt(&mut state, &stmt, &instances, &func_map);
        assert_eq!(state.get_var("x"), SVal::Real(5.0));
    }

    #[test]
    fn exec_inflow() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("level".into(), SVal::Real(5.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        // level <- 10  → level = 5 + 10 = 15
        let stmt = Stmt::FlowAssign {
            name: "level".into(),
            op: FlowOp::Inflow,
            expr: Expr::Lit(Val::Nat(10)),
        };
        exec_stmt(&mut state, &stmt, &instances, &func_map);
        assert_eq!(state.get_var("level"), SVal::Real(15.0));
    }

    #[test]
    fn exec_outflow() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("level".into(), SVal::Real(5.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        // level -> 20  → level = 5 - 20 = -15
        let stmt = Stmt::FlowAssign {
            name: "level".into(),
            op: FlowOp::Outflow,
            expr: Expr::Lit(Val::Nat(20)),
        };
        exec_stmt(&mut state, &stmt, &instances, &func_map);
        assert_eq!(state.get_var("level"), SVal::Real(-15.0));
    }

    #[test]
    fn exec_if_true_branch() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("x".into(), SVal::Real(10.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        let stmt = Stmt::IfThenElse {
            cond: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(5))),
            },
            then_branch: vec![Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(99)),
            }],
            else_branch: vec![Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(0)),
            }],
        };
        exec_stmt(&mut state, &stmt, &instances, &func_map);
        assert_eq!(state.get_var("x"), SVal::Real(99.0));
    }

    #[test]
    fn exec_if_false_branch() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("x".into(), SVal::Real(3.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        let stmt = Stmt::IfThenElse {
            cond: Expr::BinOp {
                op: BinOp::Gt,
                left: Box::new(Expr::Var("x".into())),
                right: Box::new(Expr::Lit(Val::Nat(5))),
            },
            then_branch: vec![Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(99)),
            }],
            else_branch: vec![Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(0)),
            }],
        };
        exec_stmt(&mut state, &stmt, &instances, &func_map);
        assert_eq!(state.get_var("x"), SVal::Real(0.0));
    }

    #[test]
    fn exec_call_resolves_function() {
        let mut func_map = FlowFuncMap::new();
        func_map.insert(
            ("fl".into(), "fn".into()),
            vec![Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(42)),
            }],
        );

        let mut instances = InstanceMap::new();
        instances.insert("l".into(), "fl".into());

        let mut state = FaultState {
            env: HashMap::new(),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        exec_stmt(
            &mut state,
            &Stmt::Call("l.fn".into()),
            &instances,
            &func_map,
        );
        assert_eq!(state.get_var("x"), SVal::Real(42.0));
    }

    #[test]
    fn exec_parallel_canonical_order() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("x".into(), SVal::Real(0.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        // Parallel: x = 1 | x = 2 → canonical order → x = 2
        let stmt = Stmt::Parallel(vec![
            Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(1)),
            },
            Stmt::FlowAssign {
                name: "x".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(2)),
            },
        ]);
        exec_stmt(&mut state, &stmt, &instances, &func_map);
        assert_eq!(state.get_var("x"), SVal::Real(2.0));
    }

    #[test]
    fn exec_round_snapshots_and_advances() {
        let func_map = FlowFuncMap::new();
        let instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::from([("x".into(), SVal::Real(5.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        let run_block = vec![Stmt::FlowAssign {
            name: "x".into(),
            op: FlowOp::Inflow,
            expr: Expr::Lit(Val::Nat(1)),
        }];
        let var_names = vec!["x".into()];

        // Round 0: x = 5+1 = 6, snapshot x@0=6, advance to round 1
        exec_round(&mut state, &run_block, &var_names, &instances, &func_map);
        assert_eq!(state.get_var("x"), SVal::Real(6.0));
        assert_eq!(state.round, 1);
        assert_eq!(state.read_history("x", -1), SVal::Real(6.0));

        // Round 1: x = 6+1 = 7, snapshot x@1=7, advance to round 2
        exec_round(&mut state, &run_block, &var_names, &instances, &func_map);
        assert_eq!(state.get_var("x"), SVal::Real(7.0));
        assert_eq!(state.round, 2);
        assert_eq!(state.read_history("x", -1), SVal::Real(7.0));
    }

    #[test]
    fn exec_bathtub_parallel() {
        // Simulates bathtub: level=5, inflow 10, outflow 20
        // level <- 10 → level = 5 + 10 = 15
        // level -> 20 → level = 15 - 20 = -5
        let mut func_map = FlowFuncMap::new();
        func_map.insert(
            ("faucet".into(), "in".into()),
            vec![Stmt::FlowAssign {
                name: "level".into(),
                op: FlowOp::Inflow,
                expr: Expr::Lit(Val::Nat(10)),
            }],
        );
        func_map.insert(
            ("drain".into(), "out".into()),
            vec![Stmt::FlowAssign {
                name: "level".into(),
                op: FlowOp::Outflow,
                expr: Expr::Lit(Val::Nat(20)),
            }],
        );

        let mut instances = InstanceMap::new();
        instances.insert("drawn".into(), "faucet".into());
        instances.insert("pipe".into(), "drain".into());

        let mut state = FaultState {
            env: HashMap::from([("level".into(), SVal::Real(5.0))]),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        let run_block = vec![Stmt::Parallel(vec![
            Stmt::Call("drawn.in".into()),
            Stmt::Call("pipe.out".into()),
        ])];
        let var_names = vec!["level".into()];

        exec_round(&mut state, &run_block, &var_names, &instances, &func_map);
        assert_eq!(state.get_var("level"), SVal::Real(-5.0));
    }

    #[test]
    fn exec_init_creates_instances() {
        let func_map = FlowFuncMap::new();
        let mut instances = InstanceMap::new();
        let mut state = FaultState {
            env: HashMap::new(),
            round: 0,
            comp_state: HashMap::new(),
            history: HashMap::new(),
        };

        let init_block = vec![
            Stmt::FlowAssign {
                name: "l".into(),
                op: FlowOp::Assign,
                expr: Expr::Var("new fl".into()),
            },
            Stmt::FlowAssign {
                name: "value".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(99)),
            },
        ];

        exec_init_block(&mut state, &init_block, &mut instances, &func_map);
        assert_eq!(instances.get("l"), Some(&"fl".to_string()));
        assert_eq!(state.get_var("value"), SVal::Real(99.0));
    }
}
