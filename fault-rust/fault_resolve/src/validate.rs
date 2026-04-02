//! Pre-encoding validations for parsed Fault specs.
//!
//! These checks match Go oracle error behavior:
//! - Empty function bodies
//! - Zero rounds
//! - Missing run block (no `for` or `start`)
//! - Double target swaps

use fault_syntax::{Spec, Stmt};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum FaultError {
    EmptyFunction {
        flow_name: String,
        func_name: String,
    },
    ZeroRounds,
    MissingRunBlock,
    DoubleSwap {
        instance: String,
        property: String,
    },
}

impl fmt::Display for FaultError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FaultError::EmptyFunction {
                flow_name,
                func_name,
            } => write!(
                f,
                "Error: a function cannot be empty: {}.{}",
                flow_name, func_name,
            ),
            FaultError::ZeroRounds => write!(
                f,
                "Error: run block has 0 rounds: a zero-round loop produces no states"
            ),
            FaultError::MissingRunBlock => write!(
                f,
                "Error: Fault found nothing to run. Missing run block or start block"
            ),
            FaultError::DoubleSwap { instance, property } => write!(
                f,
                "Error: property \"{}\" on {} is swapped more than once",
                property, instance,
            ),
        }
    }
}

/// Validate a parsed spec before resolution/encoding.
/// Returns all detected errors (not just the first).
pub fn validate_spec(spec: &Spec) -> Vec<FaultError> {
    let mut errors = Vec::new();

    // Check for empty function bodies
    for flow in &spec.flows {
        for (func_name, body) in &flow.funcs {
            if body.is_empty() {
                errors.push(FaultError::EmptyFunction {
                    flow_name: flow.name.clone(),
                    func_name: func_name.clone(),
                });
            }
        }
    }

    // Check run block
    match &spec.run_block {
        None => {
            // Missing run block — only error if there are no invariants either
            // (specs with just assertions but no `for` are also invalid per Go oracle)
            if spec.invariants.is_empty() || !spec.flows.is_empty() || !spec.stocks.is_empty() {
                errors.push(FaultError::MissingRunBlock);
            }
        }
        Some((rounds, init, _run)) => {
            if *rounds == 0 {
                errors.push(FaultError::ZeroRounds);
            }

            // Check for double target swaps
            check_double_swaps(init, &mut errors);
        }
    }

    errors
}

/// Detect when the same flow property is swapped more than once in the init block.
fn check_double_swaps(init_block: &[Stmt], errors: &mut Vec<FaultError>) {
    // Track: "instance.property" → count of swaps
    let mut swap_count: HashMap<String, u32> = HashMap::new();

    for stmt in init_block {
        let is_swap = match stmt {
            // `f1.target = s1` — swap to instance variable
            Stmt::FlowAssign {
                name,
                expr: fault_syntax::Expr::Var(type_ref),
                ..
            } if name.contains('.') && !type_ref.starts_with("new ") => Some(name),
            // `f2.target = f1.target` — swap to dotted reference
            Stmt::FlowAssign {
                name,
                expr: fault_syntax::Expr::Dot { .. },
                ..
            } if name.contains('.') => Some(name),
            _ => None,
        };

        if let Some(name) = is_swap {
            let count = swap_count.entry(name.clone()).or_insert(0);
            *count += 1;
            if *count > 1 {
                let parts: Vec<&str> = name.splitn(2, '.').collect();
                let (instance, property) = if parts.len() == 2 {
                    (parts[0], parts[1])
                } else {
                    (name.as_str(), "")
                };
                errors.push(FaultError::DoubleSwap {
                    instance: instance.to_string(),
                    property: property.to_string(),
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fault_syntax::*;

    fn make_spec_with_flow(funcs: Vec<(Name, Vec<Stmt>)>) -> Spec {
        Spec {
            name: "test".into(),
            constants: vec![],
            stocks: vec![StockDef {
                name: "s".into(),
                props: vec![("v".into(), Val::Nat(10))],
            }],
            flows: vec![FlowDef {
                name: "f".into(),
                stocks: vec![("target".into(), "s".into())],
                funcs,
            }],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: Some((
                1,
                vec![Stmt::FlowAssign {
                    name: "f1".into(),
                    op: FlowOp::Assign,
                    expr: Expr::Var("new f".into()),
                }],
                vec![Stmt::Call("f1.fn".into())],
            )),
        }
    }

    #[test]
    fn empty_function_detected() {
        let spec = make_spec_with_flow(vec![("fn".into(), vec![])]);
        let errs = validate_spec(&spec);
        assert_eq!(errs.len(), 1);
        assert!(matches!(&errs[0], FaultError::EmptyFunction { .. }));
    }

    #[test]
    fn nonempty_function_ok() {
        let spec = make_spec_with_flow(vec![(
            "fn".into(),
            vec![Stmt::FlowAssign {
                name: "target.v".into(),
                op: FlowOp::Assign,
                expr: Expr::Lit(Val::Nat(5)),
            }],
        )]);
        let errs = validate_spec(&spec);
        assert!(errs.is_empty());
    }

    #[test]
    fn zero_rounds_detected() {
        let spec = Spec {
            name: "test".into(),
            constants: vec![],
            stocks: vec![],
            flows: vec![],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: Some((0, vec![], vec![])),
        };
        let errs = validate_spec(&spec);
        assert_eq!(errs.len(), 1);
        assert!(matches!(&errs[0], FaultError::ZeroRounds));
    }

    #[test]
    fn missing_run_block_detected() {
        let spec = Spec {
            name: "test".into(),
            constants: vec![],
            stocks: vec![StockDef {
                name: "s".into(),
                props: vec![("v".into(), Val::Nat(10))],
            }],
            flows: vec![],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: None,
        };
        let errs = validate_spec(&spec);
        assert_eq!(errs.len(), 1);
        assert!(matches!(&errs[0], FaultError::MissingRunBlock));
    }

    #[test]
    fn double_swap_detected() {
        let spec = Spec {
            name: "test".into(),
            constants: vec![],
            stocks: vec![],
            flows: vec![],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: Some((
                1,
                vec![
                    Stmt::FlowAssign {
                        name: "f1".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Var("new f".into()),
                    },
                    Stmt::FlowAssign {
                        name: "s1".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Var("new s".into()),
                    },
                    Stmt::FlowAssign {
                        name: "s2".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Var("new s".into()),
                    },
                    Stmt::FlowAssign {
                        name: "f1.target".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Var("s1".into()),
                    },
                    Stmt::FlowAssign {
                        name: "f1.target".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Var("s2".into()),
                    },
                ],
                vec![Stmt::Call("f1.fn".into())],
            )),
        };
        let errs = validate_spec(&spec);
        assert_eq!(errs.len(), 1);
        assert!(matches!(&errs[0], FaultError::DoubleSwap { .. }));
        if let FaultError::DoubleSwap {
            instance, property, ..
        } = &errs[0]
        {
            assert_eq!(instance, "f1");
            assert_eq!(property, "target");
        }
    }

    #[test]
    fn alias_chain_double_swap_detected() {
        // aliaschain.fspec: f2.target = f1.target (Dot); f2.target = s2 (Var);
        let spec = Spec {
            name: "test".into(),
            constants: vec![],
            stocks: vec![],
            flows: vec![],
            invariants: vec![],
            import_decls: vec![],
            imported_specs: vec![],
            run_block: Some((
                1,
                vec![
                    Stmt::FlowAssign {
                        name: "f2.target".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Dot {
                            expr: Box::new(Expr::Var("f1".into())),
                            field: "target".into(),
                        },
                    },
                    Stmt::FlowAssign {
                        name: "f2.target".into(),
                        op: FlowOp::Assign,
                        expr: Expr::Var("s2".into()),
                    },
                ],
                vec![],
            )),
        };
        let errs = validate_spec(&spec);
        assert!(
            errs.iter()
                .any(|e| matches!(e, FaultError::DoubleSwap { .. }))
        );
    }

    #[test]
    fn display_format() {
        assert_eq!(
            FaultError::EmptyFunction {
                flow_name: "f".into(),
                func_name: "fn".into()
            }
            .to_string(),
            "Error: a function cannot be empty: f.fn"
        );
        assert_eq!(
            FaultError::ZeroRounds.to_string(),
            "Error: run block has 0 rounds: a zero-round loop produces no states"
        );
        assert_eq!(
            FaultError::MissingRunBlock.to_string(),
            "Error: Fault found nothing to run. Missing run block or start block"
        );
        assert_eq!(
            FaultError::DoubleSwap {
                instance: "f1".into(),
                property: "target".into()
            }
            .to_string(),
            "Error: property \"target\" on f1 is swapped more than once"
        );
    }
}
