//! SMT-LIB2 encoder: translate a ResolvedProgram into SMT constraints.
//!
//! Architecture:
//! 1. Build qualified variable names from spec + init block + flow definitions
//! 2. Emit initial value constraints
//! 3. Walk run block N rounds, SSA-versioning each assignment
//! 4. Encode assertions (negated) and assumptions (not negated)

use std::collections::HashMap;

use crate::ssa::Ssa;
use fault_resolve::ResolvedProgram;
use fault_syntax::*;

/// Collected SMT output: declarations and assertions.
struct SmtWriter {
    ssa: Ssa,
    /// (smt_name, sort) pairs to declare.
    declarations: Vec<(String, &'static str)>,
    /// SMT assertion strings.
    assertions: Vec<String>,
    /// spec name prefix.
    spec_name: String,
    /// instance_name → flow_type_name (from init block).
    instances: HashMap<String, String>,
    /// flow_type_name → { stock_ref_name → stock_type_name }.
    flow_stocks: HashMap<String, Vec<(String, String)>>,
    /// stock_type_name → [(property_name, initial_value)].
    stock_props: HashMap<String, Vec<(String, Val)>>,
    /// flow_type_name → { func_name → body }.
    flow_funcs: HashMap<String, Vec<(String, Vec<Stmt>)>>,
    /// Variables whose initial value is unknown (no constraint).
    unknown_vars: Vec<String>,
    /// Counter for generating unique block names.
    block_counter: u32,
    /// Map from unqualified/resolved names → qualified names.
    /// E.g., "s_a" → "unknowns_loop_data_a" for invariant resolution.
    name_map: HashMap<String, String>,
    /// Qualified var name → sort ("Real" or "Bool").
    var_sorts: HashMap<String, &'static str>,
    /// Per-round entry SSA versions: round → { qualified_var → versioned_name }.
    round_entries: Vec<HashMap<String, String>>,
    /// All qualified variable names (for tracking round entries).
    all_vars: Vec<String>,
    /// Optional override SSA for expression reads (used in else-branch encoding).
    read_ssa: Option<Ssa>,
}

impl SmtWriter {
    fn new(spec_name: &str) -> Self {
        Self {
            ssa: Ssa::new(),
            declarations: Vec::new(),
            assertions: Vec::new(),
            spec_name: spec_name.to_string(),
            instances: HashMap::new(),
            flow_stocks: HashMap::new(),
            stock_props: HashMap::new(),
            flow_funcs: HashMap::new(),
            unknown_vars: Vec::new(),
            block_counter: 0,
            name_map: HashMap::new(),
            var_sorts: HashMap::new(),
            round_entries: Vec::new(),
            all_vars: Vec::new(),
            read_ssa: None,
        }
    }

    /// Declare an SMT variable.
    fn declare(&mut self, name: &str, sort: &'static str) {
        self.declarations.push((name.to_string(), sort));
    }

    /// Add an assertion.
    fn assert_smt(&mut self, expr: &str) {
        self.assertions.push(format!("(assert {})", expr));
    }

    /// Build variable mappings from the program structure.
    fn build_mappings(&mut self, prog: &ResolvedProgram) {
        // Stock properties
        for stock in &prog.stocks {
            let props: Vec<(String, Val)> = stock.props.clone();
            self.stock_props.insert(stock.name.clone(), props);
        }

        // Flow stock references and functions
        for flow in &prog.flows {
            let stocks: Vec<(String, String)> = flow.stocks.clone();
            self.flow_stocks.insert(flow.name.clone(), stocks);
            let funcs: Vec<(String, Vec<Stmt>)> = flow.funcs.clone();
            self.flow_funcs.insert(flow.name.clone(), funcs);
        }

        // Instances from init block
        for stmt in &prog.init_block {
            if let Stmt::FlowAssign {
                name,
                expr: Expr::Var(type_ref),
                ..
            } = stmt
                && let Some(type_name) = type_ref.strip_prefix("new ")
            {
                self.instances.insert(name.clone(), type_name.to_string());
            }
        }
    }

    /// Get all qualified variable names and build the name mapping.
    fn build_qualified_vars(&mut self) -> Vec<(String, Val)> {
        let mut vars = Vec::new();
        let instances = self.instances.clone();
        let flow_stocks = self.flow_stocks.clone();
        let stock_props = self.stock_props.clone();

        for (inst_name, flow_type) in &instances {
            if let Some(stock_refs) = flow_stocks.get(flow_type) {
                for (stock_ref, stock_type) in stock_refs {
                    // Flow-level scalar property: stock_type is "__val_*"
                    if stock_type.starts_with("__val_") {
                        let val = parse_synthetic_val(stock_type);
                        let qname = format!("{}_{}_{}", self.spec_name, inst_name, stock_ref);

                        // Map for invariant resolution
                        let stock_key = stock_ref.clone();
                        self.name_map.insert(stock_key, qname.clone());

                        let sort = val_sort(&val);
                        self.var_sorts.insert(qname.clone(), sort);
                        vars.push((qname, val));
                        continue;
                    }

                    if let Some(props) = stock_props.get(stock_type) {
                        for (prop_name, val) in props {
                            let qname = format!(
                                "{}_{}_{}_{}",
                                self.spec_name, inst_name, stock_ref, prop_name
                            );

                            // Map stock_type_prop → qualified name
                            let stock_key = format!("{}_{}", stock_type, prop_name);
                            self.name_map.insert(stock_key, qname.clone());

                            // Map flow_type.stock_ref.prop → qualified name
                            let flow_key = format!("{}_{}_{}", flow_type, stock_ref, prop_name);
                            self.name_map.insert(flow_key, qname.clone());

                            let sort = val_sort(val);
                            self.var_sorts.insert(qname.clone(), sort);
                            vars.push((qname, val.clone()));
                        }
                    }
                }
            }
        }
        vars
    }

    /// Emit initial value declarations and constraints.
    fn encode_initial_values(&mut self) {
        let vars = self.build_qualified_vars();
        self.all_vars = vars.iter().map(|(n, _)| n.clone()).collect();

        for (qname, val) in &vars {
            let v0 = self.ssa.current_name(qname);
            let sort = self.var_sorts.get(qname).copied().unwrap_or("Real");
            self.declare(&v0, sort);

            match val {
                Val::Unknown | Val::Uncertain { .. } => {
                    self.unknown_vars.push(qname.clone());
                }
                Val::Nil => {
                    self.unknown_vars.push(qname.clone());
                }
                _ => {
                    self.assert_smt(&format!("(= {} {})", v0, val_to_smt(val)));
                }
            }
        }

        // Snapshot round 0 entry versions
        self.snapshot_round_entry();
    }

    /// Snapshot current SSA versions as round entry points for history references.
    fn snapshot_round_entry(&mut self) {
        let mut entry = HashMap::new();
        let vars = self.all_vars.clone();
        for var in &vars {
            entry.insert(var.clone(), self.ssa.current_name(var));
        }
        self.round_entries.push(entry);
    }

    /// Encode one round of the run block, then snapshot for history.
    fn encode_round(&mut self, prog: &ResolvedProgram) {
        for stmt in &prog.run_block {
            self.encode_stmt(stmt, prog);
        }
        self.snapshot_round_entry();
    }

    /// Encode a statement.
    fn encode_stmt(&mut self, stmt: &Stmt, prog: &ResolvedProgram) {
        match stmt {
            Stmt::Call(name) => self.encode_call(name, prog),
            Stmt::FlowAssign { name, op, expr } => self.encode_flow_assign(name, *op, expr),
            Stmt::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => self.encode_if(cond, then_branch, else_branch, prog),
            Stmt::Seq(stmts) => {
                for s in stmts {
                    self.encode_stmt(s, prog);
                }
            }
            Stmt::Parallel(stmts) => self.encode_parallel(stmts, prog),
            Stmt::Stay | Stmt::Advance(_) => {}
        }
    }

    /// Encode a function call: resolve instance → flow type → function body.
    fn encode_call(&mut self, call_name: &str, prog: &ResolvedProgram) {
        if let Some(dot_pos) = call_name.rfind('.') {
            let instance = &call_name[..dot_pos];
            let func_name = &call_name[dot_pos + 1..];

            if let Some(flow_type) = self.instances.get(instance).cloned()
                && let Some(funcs) = self.flow_funcs.get(&flow_type).cloned()
                && let Some((_, body)) = funcs.iter().find(|(n, _)| n == func_name)
            {
                let body = body.clone();
                for stmt in &body {
                    let resolved = self.resolve_flow_stmt(stmt, instance);
                    self.encode_stmt(&resolved, prog);
                }
            }
        }
    }

    /// Resolve variable names in a flow function body to qualified names.
    /// E.g., `vault.value` in instance `l` → `simpleA_l_vault_value`.
    fn resolve_flow_stmt(&self, stmt: &Stmt, instance: &str) -> Stmt {
        match stmt {
            Stmt::FlowAssign { name, op, expr } => {
                let qname = self.qualify_var(name, instance);
                let qexpr = self.resolve_flow_expr(expr, instance);
                Stmt::FlowAssign {
                    name: qname,
                    op: *op,
                    expr: qexpr,
                }
            }
            Stmt::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => Stmt::IfThenElse {
                cond: self.resolve_flow_expr(cond, instance),
                then_branch: then_branch
                    .iter()
                    .map(|s| self.resolve_flow_stmt(s, instance))
                    .collect(),
                else_branch: else_branch
                    .iter()
                    .map(|s| self.resolve_flow_stmt(s, instance))
                    .collect(),
            },
            Stmt::Seq(stmts) => Stmt::Seq(
                stmts
                    .iter()
                    .map(|s| self.resolve_flow_stmt(s, instance))
                    .collect(),
            ),
            Stmt::Parallel(stmts) => Stmt::Parallel(
                stmts
                    .iter()
                    .map(|s| self.resolve_flow_stmt(s, instance))
                    .collect(),
            ),
            other => other.clone(),
        }
    }

    /// Resolve a variable name to its qualified form.
    fn qualify_var(&self, name: &str, instance: &str) -> String {
        format!("{}_{}", self.spec_name, self.qualify_local(name, instance))
    }

    /// Qualify a local name (may contain dots) relative to an instance.
    /// Strips `this` prefix: `this.value` → `instance_value`.
    fn qualify_local(&self, name: &str, instance: &str) -> String {
        if name.contains('.') {
            let parts: Vec<&str> = name.split('.').collect();
            // Skip "this" prefix
            let start = if parts[0] == "this" { 1 } else { 0 };
            let mut result = instance.to_string();
            for part in &parts[start..] {
                result = format!("{}_{}", result, part);
            }
            result
        } else {
            format!("{}_{}", instance, name)
        }
    }

    /// Resolve expressions in flow function body to qualified names.
    fn resolve_flow_expr(&self, expr: &Expr, instance: &str) -> Expr {
        match expr {
            Expr::Var(name) if name == "this" => {
                Expr::Var(format!("{}_{}", self.spec_name, instance))
            }
            Expr::Var(name) if name.starts_with("this_") => {
                // Resolved `this.x` → `this_x`. Strip prefix, qualify as instance property.
                let prop = &name["this_".len()..];
                Expr::Var(format!("{}_{}_{}", self.spec_name, instance, prop))
            }
            Expr::Var(name) => Expr::Var(self.qualify_var(name, instance)),
            Expr::Dot { expr, field } => {
                let base = self.resolve_flow_expr(expr, instance);
                if let Expr::Var(base_name) = base {
                    Expr::Var(format!("{}_{}", base_name, field))
                } else {
                    Expr::Var(self.qualify_var(field, instance))
                }
            }
            Expr::BinOp { op, left, right } => Expr::BinOp {
                op: *op,
                left: Box::new(self.resolve_flow_expr(left, instance)),
                right: Box::new(self.resolve_flow_expr(right, instance)),
            },
            Expr::UnOp { op, expr } => Expr::UnOp {
                op: *op,
                expr: Box::new(self.resolve_flow_expr(expr, instance)),
            },
            Expr::History { name, offset } => Expr::History {
                name: self.qualify_var(name, instance),
                offset: *offset,
            },
            Expr::Choose(exprs) => Expr::Choose(
                exprs
                    .iter()
                    .map(|e| self.resolve_flow_expr(e, instance))
                    .collect(),
            ),
            Expr::Lit(_) => expr.clone(),
        }
    }

    /// Get the SMT sort for a variable, defaulting to "Real".
    fn sort_for(&self, qname: &str) -> &'static str {
        if let Some(s) = self.var_sorts.get(qname) {
            return s;
        }
        if let Some(i) = qname.rfind('_')
            && qname[i + 1..].chars().all(|c| c.is_ascii_digit())
            && let Some(s) = self.var_sorts.get(&qname[..i])
        {
            return s;
        }
        "Real"
    }

    /// Get the current versioned name for reading (respects read_ssa override).
    fn read_current(&mut self, name: &str) -> String {
        if let Some(ref mut rssa) = self.read_ssa {
            rssa.current_name(name)
        } else {
            self.ssa.current_name(name)
        }
    }

    /// Encode a flow assignment: `name op= expr`.
    fn encode_flow_assign(&mut self, name: &str, op: FlowOp, expr: &Expr) {
        let current = self.read_current(name);
        let rhs = self.encode_expr(expr);
        let new_name = self.ssa.next_name(name);
        let sort = self.sort_for(name);
        self.declare(&new_name, sort);

        let smt_rhs = match op {
            FlowOp::Assign => rhs,
            FlowOp::Inflow => format!("(+ {} {})", current, rhs),
            FlowOp::Outflow => format!("(- {} {})", current, rhs),
        };

        self.assert_smt(&format!("(= {} {})", new_name, smt_rhs));
    }

    /// Encode an expression to SMT-LIB2 string, using current SSA versions.
    fn encode_expr(&mut self, expr: &Expr) -> String {
        match expr {
            Expr::Lit(val) => val_to_smt(val),
            Expr::Var(name) => self.read_current(name),
            Expr::BinOp { op, left, right } => {
                let l = self.encode_expr(left);
                let r = self.encode_expr(right);
                format!("({} {} {})", binop_to_smt(*op), l, r)
            }
            Expr::UnOp { op, expr } => {
                let e = self.encode_expr(expr);
                format!("({} {})", unop_to_smt(*op), e)
            }
            Expr::History { name, offset } => {
                // Use round_entries to find the version at the referenced round.
                // Current round index = round_entries.len() - 1 (last snapshot).
                // [now-k] at round R → entry at round R-k (which is index R+1-k
                // because entry[0] = initial, entry[1] = after round 0, etc.)
                let current_round = self.round_entries.len().saturating_sub(1);
                let target_round = current_round as i64 + offset;
                if target_round >= 0
                    && (target_round as usize) < self.round_entries.len()
                    && let Some(ver) = self.round_entries[target_round as usize].get(name)
                {
                    return ver.clone();
                }
                // Fallback: use initial version
                format!("{}_0", name)
            }
            Expr::Dot { expr, field } => {
                let base = self.encode_expr(expr);
                // Shouldn't occur after resolution, but handle gracefully
                format!("{}_{}", base.trim_end_matches(')'), field)
            }
            Expr::Choose(exprs) => {
                if exprs.is_empty() {
                    "0.0".into()
                } else {
                    // Nondeterministic: generate fresh variable
                    self.encode_expr(&exprs[0])
                }
            }
        }
    }

    /// Encode an if-then-else with branch tracking.
    ///
    /// Both branches are encoded sequentially. The then branch runs first,
    /// then the else branch uses `read_ssa` to read pre-branch values while
    /// writing to sequential SSA versions.
    fn encode_if(
        &mut self,
        cond: &Expr,
        then_branch: &[Stmt],
        else_branch: &[Stmt],
        prog: &ResolvedProgram,
    ) {
        let cond_smt = self.encode_expr(cond);

        let ssa_before = self.ssa.clone();

        let then_modified = collect_modified_vars(then_branch);
        let else_modified = collect_modified_vars(else_branch);

        let mut all_modified = then_modified.clone();
        for v in &else_modified {
            if !all_modified.contains(v) {
                all_modified.push(v.clone());
            }
        }

        // Encode then branch (reads from current SSA, writes next versions)
        for stmt in then_branch {
            self.encode_stmt(stmt, prog);
        }
        let mut ssa_after_then = self.ssa.clone();

        // Encode else branch: reads from pre-branch SSA, writes sequential
        if !else_branch.is_empty() {
            self.read_ssa = Some(ssa_before.clone());
            for stmt in else_branch {
                self.encode_stmt(stmt, prog);
            }
            self.read_ssa = None;
        }
        let mut ssa_after_else = self.ssa.clone();

        // Capture branch versions and create phi.
        // Then version = what encode produced in then branch.
        // Else version: if the var was modified in else, use ssa_after_else;
        // otherwise use ssa_before (unchanged).
        let mut then_vers = Vec::new();
        let mut else_vers = Vec::new();
        let mut phi_vers = Vec::new();

        for var in &all_modified {
            let then_v = if then_modified.contains(var) {
                ssa_after_then.current_name(var)
            } else {
                ssa_before.clone().current_name(var)
            };
            let else_v = if else_modified.contains(var) {
                ssa_after_else.current_name(var)
            } else {
                ssa_before.clone().current_name(var)
            };
            then_vers.push(then_v);
            else_vers.push(else_v);

            let phi = self.ssa.next_name(var);
            let sort = self.sort_for(var);
            self.declare(&phi, sort);
            phi_vers.push(phi);
        }

        // Block tracking booleans — separate IDs for then/else
        self.block_counter += 1;
        let then_block_id = self.block_counter;
        self.block_counter += 1;
        let else_block_id = self.block_counter;

        let round_num = self.round_entries.len();
        let true_name = format!("block{}true_{}", then_block_id, round_num);
        let false_name = format!("block{}false_{}", else_block_id, round_num);
        self.declare(&true_name, "Bool");
        self.declare(&false_name, "Bool");

        if !all_modified.is_empty() {
            let mut then_parts = vec![
                format!("(= {} true)", true_name),
                format!("(= {} false)", false_name),
            ];
            for (phi, then_v) in phi_vers.iter().zip(then_vers.iter()) {
                then_parts.push(format!("(= {} {})", phi, then_v));
            }

            let mut else_parts = vec![
                format!("(= {} false)", true_name),
                format!("(= {} true)", false_name),
            ];
            for (phi, else_v) in phi_vers.iter().zip(else_vers.iter()) {
                else_parts.push(format!("(= {} {})", phi, else_v));
            }

            let then_conj = format!("(and {})", then_parts.join(" "));
            let else_conj = format!("(and {})", else_parts.join(" "));

            self.assert_smt(&format!("(ite {} {} {})", cond_smt, then_conj, else_conj));

            self.assert_smt(&format!(
                "(or (and {}\n(not {}))\n(and (not {})\n{}))",
                true_name, false_name, true_name, false_name
            ));
        }
    }

    /// Encode parallel execution: all permutations.
    fn encode_parallel(&mut self, stmts: &[Stmt], prog: &ResolvedProgram) {
        // For now, use canonical order (like exec does).
        // TODO: generate permutation disjuncts for full nondeterminism.
        for s in stmts {
            self.encode_stmt(s, prog);
        }
    }

    /// Encode invariants (assertions and assumptions).
    fn encode_invariants(&mut self, prog: &ResolvedProgram) {
        // For each invariant, generate temporal constraint over all round versions
        let num_rounds = prog.rounds;

        for inv in &prog.invariants {
            match inv {
                Invariant::Assert { expr, temporal } => {
                    let negated = self.encode_temporal_negated(expr, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", negated));
                }
                Invariant::Assume { expr, temporal } => {
                    let assumed = self.encode_temporal(expr, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", assumed));
                }
                Invariant::AssertWhen {
                    guard,
                    body,
                    temporal,
                } => {
                    let negated =
                        self.encode_when_temporal_negated(guard, body, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", negated));
                }
                Invariant::AssumeWhen {
                    guard,
                    body,
                    temporal,
                } => {
                    let assumed = self.encode_when_temporal(guard, body, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", assumed));
                }
            }
        }
    }

    /// Encode a temporal property (not negated, for assumptions).
    fn encode_temporal(&self, expr: &Expr, temporal: &Temporal, num_rounds: u64) -> String {
        let round_exprs: Vec<String> = (0..=num_rounds)
            .map(|r| self.encode_expr_at_round(expr, r))
            .collect();

        match temporal {
            Temporal::Always => format!("(and {})", round_exprs.join(" ")),
            Temporal::Eventually => format!("(or {})", round_exprs.join(" ")),
            Temporal::EventuallyAlways => {
                // (or P_N (and P_{N-1} P_N) ... (and P_0 ... P_N))
                let n = num_rounds as usize;
                let suffixes: Vec<String> = (0..=n)
                    .map(|k| {
                        let conj: Vec<&str> =
                            round_exprs[k..=n].iter().map(|s| s.as_str()).collect();
                        if conj.len() == 1 {
                            conj[0].to_string()
                        } else {
                            format!("(and {})", conj.join(" "))
                        }
                    })
                    .collect();
                format!("(or {})", suffixes.join(" "))
            }
            Temporal::Nmt(n) => {
                // At most n: negate "at least n+1"
                encode_at_most(&round_exprs, *n)
            }
            Temporal::Nft(n) => {
                // At least n: OR of all C(N+1, n) subsets
                encode_at_least(&round_exprs, *n)
            }
        }
    }

    /// Encode a negated temporal property (for assertions → counterexample search).
    fn encode_temporal_negated(&self, expr: &Expr, temporal: &Temporal, num_rounds: u64) -> String {
        let round_exprs: Vec<String> = (0..=num_rounds)
            .map(|r| self.encode_expr_at_round(expr, r))
            .collect();

        // Negate: always → or(not), eventually → and(not), etc.
        match temporal {
            Temporal::Always => {
                let negated: Vec<String> =
                    round_exprs.iter().map(|e| format!("(not {})", e)).collect();
                format!("(or {})", negated.join(" "))
            }
            Temporal::Eventually => {
                let negated: Vec<String> =
                    round_exprs.iter().map(|e| format!("(not {})", e)).collect();
                format!("(and {})", negated.join(" "))
            }
            _ => {
                // For complex temporals, negate the whole thing
                let pos = self.encode_temporal(expr, temporal, num_rounds);
                format!("(not {})", pos)
            }
        }
    }

    /// Encode when...then (conditional) temporal not negated.
    fn encode_when_temporal(
        &self,
        guard: &Expr,
        body: &Expr,
        temporal: &Temporal,
        num_rounds: u64,
    ) -> String {
        let round_exprs: Vec<String> = (0..=num_rounds)
            .map(|r| {
                let g = self.encode_expr_at_round(guard, r);
                let b = self.encode_expr_at_round(body, r);
                format!("(=> {} {})", g, b)
            })
            .collect();

        match temporal {
            Temporal::Always => format!("(and {})", round_exprs.join(" ")),
            Temporal::Eventually => format!("(or {})", round_exprs.join(" ")),
            _ => format!("(and {})", round_exprs.join(" ")),
        }
    }

    /// Encode when...then (conditional) temporal negated (for assertions).
    fn encode_when_temporal_negated(
        &self,
        guard: &Expr,
        body: &Expr,
        temporal: &Temporal,
        num_rounds: u64,
    ) -> String {
        let pos = self.encode_when_temporal(guard, body, temporal, num_rounds);
        format!("(not {})", pos)
    }

    /// Encode an expression using variable versions at a specific round.
    fn encode_expr_at_round(&self, expr: &Expr, round: u64) -> String {
        match expr {
            Expr::Lit(val) => val_to_smt(val),
            Expr::Var(name) => {
                // Resolve through name_map (invariant stock refs → qualified)
                let resolved = self.name_map.get(name).cloned().unwrap_or(name.clone());
                format!("{}_{}", resolved, round)
            }
            Expr::BinOp { op, left, right } => {
                let l = self.encode_expr_at_round(left, round);
                let r = self.encode_expr_at_round(right, round);
                format!("({} {} {})", binop_to_smt(*op), l, r)
            }
            Expr::UnOp { op, expr } => {
                let e = self.encode_expr_at_round(expr, round);
                format!("({} {})", unop_to_smt(*op), e)
            }
            _ => "0.0".into(),
        }
    }

    /// Produce the final SMT-LIB2 string.
    fn emit(&self) -> String {
        let mut out = String::new();
        out.push_str("(set-logic QF_NRA)\n");

        for (name, sort) in &self.declarations {
            out.push_str(&format!("(declare-fun {} () {})\n", name, sort));
        }

        for assertion in &self.assertions {
            out.push_str(assertion);
            out.push('\n');
        }

        out
    }
}

// ── Top-level entry point ───────────────────────────────────────────

/// Encode a resolved program into SMT-LIB2 string.
pub fn encode_program(prog: &ResolvedProgram, spec_name: &str) -> String {
    let mut w = SmtWriter::new(spec_name);
    w.build_mappings(prog);
    w.encode_initial_values();

    for _ in 0..prog.rounds {
        w.encode_round(prog);
    }

    w.encode_invariants(prog);
    w.emit()
}

// ── Helpers ─────────────────────────────────────────────────────────

/// Determine the SMT sort for a value.
fn val_sort(val: &Val) -> &'static str {
    match val {
        Val::Bool(_) => "Bool",
        _ => "Real",
    }
}

/// Parse a synthetic stock type name (e.g., `__val_0`) back to a Val.
fn parse_synthetic_val(stock_type: &str) -> Val {
    let suffix = stock_type.strip_prefix("__val_").unwrap_or("0");
    if suffix == "true" {
        Val::Bool(true)
    } else if suffix == "false" {
        Val::Bool(false)
    } else if let Ok(n) = suffix.parse::<u64>() {
        Val::Nat(n)
    } else if let Ok(f) = suffix.parse::<f64>() {
        Val::Float(f)
    } else {
        Val::Nat(0)
    }
}

/// Convert a Val to SMT-LIB2 literal string.
fn val_to_smt(val: &Val) -> String {
    match val {
        Val::Nat(n) => format!("{}.0", n),
        Val::Float(f) => {
            let s = format!("{}", f);
            if s.contains('.') {
                s
            } else {
                format!("{}.0", s)
            }
        }
        Val::Bool(b) => if *b { "true" } else { "false" }.into(),
        Val::Str(_) => "false".into(),
        Val::Unknown | Val::Uncertain { .. } | Val::Nil => "0.0".into(),
    }
}

/// Convert a BinOp to SMT-LIB2 operator string.
fn binop_to_smt(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "mod",
        BinOp::Exp => "^",
        BinOp::Eq => "=",
        BinOp::Neq => "distinct",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        _ => "unknown_op",
    }
}

/// Convert a UnOp to SMT-LIB2 operator string.
fn unop_to_smt(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "-",
        UnOp::Not => "not",
    }
}

/// Collect all variable names modified in a list of statements.
fn collect_modified_vars(stmts: &[Stmt]) -> Vec<String> {
    let mut vars = Vec::new();
    for stmt in stmts {
        collect_modified_in_stmt(stmt, &mut vars);
    }
    vars
}

fn collect_modified_in_stmt(stmt: &Stmt, vars: &mut Vec<String>) {
    match stmt {
        Stmt::FlowAssign { name, .. } => {
            if !vars.contains(name) {
                vars.push(name.clone());
            }
        }
        Stmt::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => {
            for s in then_branch {
                collect_modified_in_stmt(s, vars);
            }
            for s in else_branch {
                collect_modified_in_stmt(s, vars);
            }
        }
        Stmt::Seq(stmts) | Stmt::Parallel(stmts) => {
            for s in stmts {
                collect_modified_in_stmt(s, vars);
            }
        }
        _ => {}
    }
}

/// Encode "at most n of these are true".
fn encode_at_most(exprs: &[String], n: u64) -> String {
    if n as usize >= exprs.len() {
        "true".into()
    } else {
        // At most n ≡ ¬(at least n+1)
        let at_least = encode_at_least(exprs, n + 1);
        format!("(not {})", at_least)
    }
}

/// Encode "at least n of these are true".
fn encode_at_least(exprs: &[String], n: u64) -> String {
    if n == 0 {
        return "true".into();
    }
    if n as usize > exprs.len() {
        return "false".into();
    }

    let subsets = combinations(exprs.len(), n as usize);
    let disjuncts: Vec<String> = subsets
        .iter()
        .map(|subset| {
            let conj: Vec<&str> = subset.iter().map(|&i| exprs[i].as_str()).collect();
            if conj.len() == 1 {
                conj[0].to_string()
            } else {
                format!("(and {})", conj.join(" "))
            }
        })
        .collect();

    if disjuncts.len() == 1 {
        disjuncts[0].clone()
    } else {
        format!("(or {})", disjuncts.join(" "))
    }
}

/// Generate all combinations of `n` choose `k`.
fn combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    let mut current = Vec::new();
    combinations_helper(n, k, 0, &mut current, &mut result);
    result
}

fn combinations_helper(
    n: usize,
    k: usize,
    start: usize,
    current: &mut Vec<usize>,
    result: &mut Vec<Vec<usize>>,
) {
    if current.len() == k {
        result.push(current.clone());
        return;
    }
    for i in start..n {
        current.push(i);
        combinations_helper(n, k, i + 1, current, result);
        current.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn val_to_smt_literals() {
        assert_eq!(val_to_smt(&Val::Nat(30)), "30.0");
        assert_eq!(val_to_smt(&Val::Float(3.14)), "3.14");
        assert_eq!(val_to_smt(&Val::Bool(true)), "true");
        assert_eq!(val_to_smt(&Val::Str("hi".into())), "false");
    }

    #[test]
    fn binop_to_smt_ops() {
        assert_eq!(binop_to_smt(BinOp::Add), "+");
        assert_eq!(binop_to_smt(BinOp::Sub), "-");
        assert_eq!(binop_to_smt(BinOp::Eq), "=");
        assert_eq!(binop_to_smt(BinOp::Gt), ">");
    }

    #[test]
    fn combinations_3_2() {
        let result = combinations(3, 2);
        assert_eq!(result, vec![vec![0, 1], vec![0, 2], vec![1, 2]]);
    }

    #[test]
    fn encode_at_least_2_of_3() {
        let exprs: Vec<String> = vec!["P0".into(), "P1".into(), "P2".into()];
        let result = encode_at_least(&exprs, 2);
        assert!(result.contains("(and P0 P1)"));
        assert!(result.contains("(and P0 P2)"));
        assert!(result.contains("(and P1 P2)"));
    }

    #[test]
    fn encode_simple_program() {
        // Minimal test: spec with one stock, one flow, one round
        let prog = ResolvedProgram {
            stocks: vec![StockDef {
                name: "st".into(),
                props: vec![("value".into(), Val::Nat(30))],
            }],
            flows: vec![FlowDef {
                name: "fl".into(),
                stocks: vec![("vault".into(), "st".into())],
                funcs: vec![(
                    "fn".into(),
                    vec![Stmt::FlowAssign {
                        name: "vault.value".into(),
                        op: FlowOp::Inflow,
                        expr: Expr::BinOp {
                            op: BinOp::Sub,
                            left: Box::new(Expr::Var("vault.value".into())),
                            right: Box::new(Expr::Lit(Val::Nat(2))),
                        },
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
        };

        let smt = encode_program(&prog, "test");
        assert!(smt.contains("(set-logic QF_NRA)"));
        assert!(smt.contains("test_l_vault_value_0"));
        assert!(smt.contains("(= test_l_vault_value_0 30.0)"));
        assert!(smt.contains("test_l_vault_value_1"));
    }

    #[test]
    fn encode_unknown_var() {
        // Unknown variable: no initial constraint
        let prog = ResolvedProgram {
            stocks: vec![StockDef {
                name: "s".into(),
                props: vec![("a".into(), Val::Unknown), ("b".into(), Val::Nat(2))],
            }],
            flows: vec![FlowDef {
                name: "f".into(),
                stocks: vec![("data".into(), "s".into())],
                funcs: vec![],
            }],
            constants: vec![],
            components: vec![],
            invariants: vec![],
            start_states: vec![],
            rounds: 0,
            init_block: vec![Stmt::FlowAssign {
                name: "loop".into(),
                op: FlowOp::Assign,
                expr: Expr::Var("new f".into()),
            }],
            run_block: vec![],
            var_names: vec!["a".into(), "b".into()],
        };

        let smt = encode_program(&prog, "unknowns");
        // `a` is unknown → declared but no initial constraint
        assert!(smt.contains("unknowns_loop_data_a_0"));
        assert!(!smt.contains("(= unknowns_loop_data_a_0"));
        // `b` has value → initial constraint
        assert!(smt.contains("(= unknowns_loop_data_b_0 2.0)"));
    }

    // ── Integration tests: parse → resolve → encode ─────────────────

    /// Helper: normalize SMT for comparison (strip blank lines, trim).
    fn normalize_smt(s: &str) -> Vec<String> {
        s.lines()
            .map(|l| l.trim().to_string())
            .filter(|l| !l.is_empty())
            .collect()
    }

    #[test]
    fn e2e_unknowns() {
        let src = r#"spec unknowns;

def s = stock{
    a,
    b: 2,
    c: 0,
};

def f = flow{
    data: new s,
    fn: func{
       data.c <- data.a + data.b;
    },
};

assume s.a > 5;
assert s.a <= 6;

for 3 init{loop = new f;} run {
    loop.fn;
}"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // Declarations
        assert!(lines.contains(&"(set-logic QF_NRA)".into()));
        assert!(lines.contains(&"(declare-fun unknowns_loop_data_a_0 () Real)".into()));
        assert!(lines.contains(&"(declare-fun unknowns_loop_data_b_0 () Real)".into()));
        assert!(lines.contains(&"(declare-fun unknowns_loop_data_c_0 () Real)".into()));
        assert!(lines.contains(&"(declare-fun unknowns_loop_data_c_1 () Real)".into()));
        assert!(lines.contains(&"(declare-fun unknowns_loop_data_c_2 () Real)".into()));
        assert!(lines.contains(&"(declare-fun unknowns_loop_data_c_3 () Real)".into()));

        // Initial values
        assert!(lines.contains(&"(assert (= unknowns_loop_data_b_0 2.0))".into()));
        assert!(lines.contains(&"(assert (= unknowns_loop_data_c_0 0.0))".into()));
        // No initial constraint for a (unknown)
        assert!(!smt.contains("(= unknowns_loop_data_a_0"));

        // Round assignments
        assert!(lines.contains(
            &"(assert (= unknowns_loop_data_c_1 (+ unknowns_loop_data_c_0 (+ unknowns_loop_data_a_0 unknowns_loop_data_b_0))))"
                .into()
        ));
    }

    #[test]
    fn e2e_asserts() {
        let src = r#"spec asserts;

def fsample = flow{
    target: new ssample,
    fn: func{
        target.value -> target.value/2;
    },
};

def ssample = stock{
    value: 40,
};

assert ssample.value == 40;
assume fsample.target.value > 2;

for 4 init{test = new fsample;} run {
    test.fn;
}"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // Initial value
        assert!(lines.contains(&"(assert (= asserts_test_target_value_0 40.0))".into()));

        // Outflow: target.value -> target.value/2  →  val_new = val_old - (val_old/2)
        assert!(lines.contains(
            &"(assert (= asserts_test_target_value_1 (- asserts_test_target_value_0 (/ asserts_test_target_value_0 2.0))))"
                .into()
        ));

        // Assertion negated (or of not-equal for each round)
        assert!(smt.contains("(or (not (= asserts_test_target_value_0 40.0))"));

        // Assumption not negated (and of greater-than for each round)
        assert!(smt.contains("(and (> asserts_test_target_value_0 2.0)"));
    }

    #[test]
    fn e2e_simple_a() {
        let src = r#"spec simpleA;

def st = stock{
    value: 30,
};

def fl = flow{
    active: false,
    vault: new st,
    fn: func{
        if vault.value > 4 {
           vault.value <- vault.value - 2;
        }
    },
};

for 1 init{l = new fl;} run {
    l.fn;
}"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // Declarations
        assert!(lines.contains(&"(declare-fun simpleA_l_vault_value_0 () Real)".into()));
        assert!(lines.contains(&"(declare-fun simpleA_l_vault_value_1 () Real)".into()));
        assert!(lines.contains(&"(declare-fun simpleA_l_vault_value_2 () Real)".into()));

        // Initial value
        assert!(lines.contains(&"(assert (= simpleA_l_vault_value_0 30.0))".into()));

        // Inflow assignment inside if: val_1 = val_0 + (val_0 - 2.0)
        assert!(lines.contains(
            &"(assert (= simpleA_l_vault_value_1 (+ simpleA_l_vault_value_0 (- simpleA_l_vault_value_0 2.0))))"
                .into()
        ));

        // ITE with phi
        assert!(smt.contains("(ite (> simpleA_l_vault_value_0 4.0)"));
        assert!(smt.contains("simpleA_l_vault_value_2 simpleA_l_vault_value_1"));
        assert!(smt.contains("simpleA_l_vault_value_2 simpleA_l_vault_value_0"));
    }

    #[test]
    fn e2e_booleans() {
        let src = r#"spec booleans;

def st = stock{
    value: true,
};

def fl = flow{
    vault: new st,
    fn: func{
        if vault.value {
            vault.value = false;
        }else{
            vault.value = true;
        }
    },
};

for 1 init{l = new fl;} run {
    l.fn;
}"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // Bool-sorted declarations
        assert!(lines.contains(&"(declare-fun booleans_l_vault_value_0 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun booleans_l_vault_value_1 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun booleans_l_vault_value_2 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun booleans_l_vault_value_3 () Bool)".into()));

        // Initial value
        assert!(lines.contains(&"(assert (= booleans_l_vault_value_0 true))".into()));

        // Then: false, Else: true
        assert!(lines.contains(&"(assert (= booleans_l_vault_value_1 false))".into()));
        assert!(lines.contains(&"(assert (= booleans_l_vault_value_2 true))".into()));

        // ITE using the boolean value directly as condition
        assert!(smt.contains("(ite booleans_l_vault_value_0"));
    }

    #[test]
    fn e2e_increment() {
        let src = r#"spec increment;

def fib = flow{
    value: 0,
    step: func{
        if this.value == 0 {
              this.value = 1;
        }else{
              this.value <- this.value[now-1];
        }
    }
};

for 5 init{f = new fib;} run{
    f.step;
}"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // Flow-level scalar property
        assert!(lines.contains(&"(declare-fun increment_f_value_0 () Real)".into()));
        assert!(lines.contains(&"(assert (= increment_f_value_0 0.0))".into()));

        // 5 rounds × 3 versions + initial = 16 value versions (0..15)
        assert!(lines.contains(&"(declare-fun increment_f_value_15 () Real)".into()));

        // Then branch: this.value = 1
        assert!(lines.contains(&"(assert (= increment_f_value_1 1.0))".into()));

        // Else branch: this.value <- this.value[now-1]
        // Round 1: value_2 = value_0 + value_0 (history[now-1] = initial)
        assert!(lines.contains(
            &"(assert (= increment_f_value_2 (+ increment_f_value_0 increment_f_value_0)))".into()
        ));

        // Round 2: value_5 = value_3 + value_0 (history[now-1] = round 0 entry)
        assert!(lines.contains(
            &"(assert (= increment_f_value_5 (+ increment_f_value_3 increment_f_value_0)))".into()
        ));

        // ITE condition uses qualified name (not this_value)
        assert!(smt.contains("(ite (= increment_f_value_0 0.0)"));
    }

    #[test]
    fn e2e_history1() {
        let src = r#"spec history1;

def counter = flow{
    value: 1,
    step: func{
        if this.value > 0 {
            this.value <- this.value[now-1];
        } else {
            this.value = 1;
        }
    }
};

for 4 init{c = new counter;} run{
    c.step;
}"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        assert!(lines.contains(&"(assert (= history1_c_value_0 1.0))".into()));

        // Round 1 then: value_1 = value_0 + value_0 (inflow, history[now-1]=value_0)
        assert!(lines.contains(
            &"(assert (= history1_c_value_1 (+ history1_c_value_0 history1_c_value_0)))".into()
        ));

        // Round 2 then: value_4 = value_3 + value_0
        assert!(lines.contains(
            &"(assert (= history1_c_value_4 (+ history1_c_value_3 history1_c_value_0)))".into()
        ));

        // Round 3 then: value_7 = value_6 + value_3
        assert!(lines.contains(
            &"(assert (= history1_c_value_7 (+ history1_c_value_6 history1_c_value_3)))".into()
        ));
    }
}
