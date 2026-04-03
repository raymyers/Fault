//! SMT-LIB2 encoder: translate a ResolvedProgram into SMT constraints.
//!
//! Architecture:
//! 1. Build qualified variable names from spec + init block + flow definitions
//! 2. Emit initial value constraints
//! 3. Walk run block N rounds, SSA-versioning each assignment
//! 4. Encode assertions (negated) and assumptions (not negated)

use std::collections::{BTreeMap, HashSet};

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
    instances: BTreeMap<String, String>,
    /// flow_type_name → { stock_ref_name → stock_type_name }.
    flow_stocks: BTreeMap<String, Vec<(String, String)>>,
    /// stock_type_name → [(property_name, initial_value)].
    stock_props: BTreeMap<String, Vec<(String, Val)>>,
    /// flow_type_name → { func_name → body }.
    flow_funcs: BTreeMap<String, Vec<(String, Vec<Stmt>)>>,
    /// Variables whose initial value is unknown (no constraint).
    unknown_vars: Vec<String>,
    /// Counter for generating unique block names.
    block_counter: u32,
    /// Map from unqualified/resolved names → qualified names.
    /// E.g., "s_a" → "unknowns_loop_data_a" for invariant resolution.
    name_map: BTreeMap<String, String>,
    /// Qualified var name → sort ("Real" or "Bool").
    var_sorts: BTreeMap<String, &'static str>,
    /// Stock target reassignments from init: "inst.stock_ref" → "target_instance".
    target_swaps: BTreeMap<String, String>,
    /// Property value overrides from init: "inst.prop" → override value.
    prop_overrides: BTreeMap<String, Val>,
    /// Per-round entry SSA versions: round → { qualified_var → versioned_name }.
    round_entries: Vec<BTreeMap<String, String>>,
    /// All qualified variable names (for tracking round entries).
    all_vars: Vec<String>,
    /// Optional override SSA for expression reads (used in else-branch/parallel encoding).
    read_ssa: Option<Ssa>,
    /// Track already-declared SMT variables to avoid duplicates.
    declared: HashSet<String>,
}

impl SmtWriter {
    fn new(spec_name: &str) -> Self {
        Self {
            ssa: Ssa::new(),
            declarations: Vec::new(),
            assertions: Vec::new(),
            spec_name: spec_name.to_string(),
            instances: BTreeMap::new(),
            flow_stocks: BTreeMap::new(),
            stock_props: BTreeMap::new(),
            flow_funcs: BTreeMap::new(),
            unknown_vars: Vec::new(),
            block_counter: 0,
            name_map: BTreeMap::new(),
            var_sorts: BTreeMap::new(),
            target_swaps: BTreeMap::new(),
            prop_overrides: BTreeMap::new(),
            round_entries: Vec::new(),
            all_vars: Vec::new(),
            read_ssa: None,
            declared: HashSet::new(),
        }
    }

    /// Declare an SMT variable.
    fn declare(&mut self, name: &str, sort: &'static str) {
        if self.declared.insert(name.to_string()) {
            self.declarations.push((name.to_string(), sort));
        }
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

        // Process init block: instances, target swaps, property overrides
        for stmt in &prog.init_block {
            match stmt {
                Stmt::FlowAssign {
                    name,
                    op: _,
                    expr: Expr::Var(type_ref),
                } => {
                    if let Some(type_name) = type_ref.strip_prefix("new ") {
                        // Instance creation: `inst = new Type`
                        self.instances.insert(name.clone(), type_name.to_string());
                    } else if name.contains('.') {
                        // Target swap: `flow_inst.stock_ref = other_inst`
                        self.target_swaps.insert(name.clone(), type_ref.clone());
                    }
                }
                Stmt::FlowAssign {
                    name,
                    op: _,
                    expr: Expr::Lit(val),
                } => {
                    if name.contains('.') {
                        // Property override: `inst.prop = val`
                        self.prop_overrides.insert(name.clone(), val.clone());
                    }
                }
                _ => {}
            }
        }
    }

    /// Get all qualified variable names and build the name mapping.
    fn build_qualified_vars(&mut self) -> Vec<(String, Val)> {
        let mut vars = Vec::new();
        let instances = self.instances.clone();
        let flow_stocks = self.flow_stocks.clone();
        let stock_props = self.stock_props.clone();
        let target_swaps = self.target_swaps.clone();
        let prop_overrides = self.prop_overrides.clone();
        // Track which stock instances are already emitted (avoid duplicates
        // when multiple flows reference the same swapped target)
        let mut emitted: std::collections::HashSet<String> = std::collections::HashSet::new();

        for (inst_name, flow_type) in &instances {
            if let Some(stock_refs) = flow_stocks.get(flow_type) {
                for (stock_ref, stock_type) in stock_refs {
                    // Check for target swap: flow_inst.stock_ref → other_instance
                    let swap_key = format!("{}.{}", inst_name, stock_ref);
                    let (var_prefix, resolved_stock_type) =
                        if let Some(target_inst) = target_swaps.get(&swap_key) {
                            // Swapped: use target instance name and its stock type
                            let tgt_type = instances
                                .get(target_inst)
                                .cloned()
                                .unwrap_or(stock_type.clone());
                            (target_inst.clone(), tgt_type)
                        } else {
                            // Not swapped: use flow_inst_stock_ref as prefix
                            (format!("{}_{}", inst_name, stock_ref), stock_type.clone())
                        };

                    // Flow-level scalar property: stock_type is "__val_*"
                    if resolved_stock_type.starts_with("__val_") {
                        let val = parse_synthetic_val(&resolved_stock_type);
                        let qname = format!("{}_{}", self.spec_name, var_prefix);
                        if !emitted.insert(qname.clone()) {
                            continue;
                        }

                        let stock_key = stock_ref.clone();
                        self.name_map.insert(stock_key, qname.clone());

                        let sort = val_sort(&val);
                        self.var_sorts.insert(qname.clone(), sort);
                        vars.push((qname, val));
                        continue;
                    }

                    if let Some(props) = stock_props.get(&resolved_stock_type) {
                        for (prop_name, template_val) in props {
                            let qname = format!("{}_{}_{}", self.spec_name, var_prefix, prop_name);

                            // Always add name_map entries (even for duplicate vars)
                            let stock_key = format!("{}_{}", resolved_stock_type, prop_name);
                            self.name_map.insert(stock_key, qname.clone());
                            let flow_key = format!("{}_{}_{}", flow_type, stock_ref, prop_name);
                            self.name_map.insert(flow_key, qname.clone());
                            let inst_key = format!("{}_{}_{}", inst_name, stock_ref, prop_name);
                            self.name_map.insert(inst_key, qname.clone());

                            // Only emit declaration once
                            if !emitted.insert(qname.clone()) {
                                continue;
                            }

                            let override_key = format!("{}.{}", var_prefix, prop_name);
                            let val = prop_overrides
                                .get(&override_key)
                                .cloned()
                                .unwrap_or(template_val.clone());

                            let sort = val_sort(&val);
                            self.var_sorts.insert(qname.clone(), sort);
                            vars.push((qname, val));
                        }
                    }
                }
            }
        }
        vars
    }

    /// Encode constant definitions as Bool declarations and constraints.
    ///
    /// String literal constants → free Bool (no constraint).
    /// Expression constants → declare + assert defining expression.
    /// Negation `!x` → intermediate `x_neg` variable.
    fn encode_constants(&mut self, prog: &ResolvedProgram) {
        // First pass: register names and declare literal (non-expr) constants
        for cdef in &prog.constants {
            let qname = format!("{}_{}", self.spec_name, cdef.name);
            self.name_map.insert(cdef.name.clone(), qname.clone());
            let sort = const_sort(&cdef.value, cdef.expr.is_some());
            self.var_sorts.insert(qname.clone(), sort);
            if cdef.expr.is_none() {
                self.declare(&format!("{}_0", qname), sort);
            }
        }
        // Register imported constants with their original spec prefix.
        // The assertion resolver converts Dot(alias, name) → Var("alias_name"),
        // so we register "alias_name" → "{imported_spec_name}_name".
        for (spec_name, consts) in &prog.imported_constants {
            for cdef in consts {
                let qname = format!("{}_{}", spec_name, cdef.name);
                // Map alias_name → imported_spec_name (for each known alias)
                for (alias, sname) in &prog.import_alias_map {
                    if sname == spec_name {
                        let alias_key = format!("{}_{}", alias, cdef.name);
                        self.name_map.insert(alias_key, qname.clone());
                    }
                }
                self.name_map.insert(cdef.name.clone(), qname.clone());
                let sort = const_sort(&cdef.value, cdef.expr.is_some());
                self.var_sorts.insert(qname.clone(), sort);
                if cdef.expr.is_none() {
                    self.declare(&format!("{}_0", qname), sort);
                }
            }
        }
        // Second pass: process expression constants (intermediates declared first)
        for cdef in &prog.constants {
            if let Some(expr) = &cdef.expr {
                let qname = format!("{}_{}", self.spec_name, cdef.name);
                let v0 = format!("{}_0", qname);
                let rhs = self.encode_const_expr(expr, true);
                // Declare the derived constant after intermediates
                self.declare(&v0, "Bool");
                self.assert_smt(&format!("(= {} {})", v0, rhs));
            }
        }
        // Process imported expression constants
        for (spec_name, consts) in &prog.imported_constants {
            for cdef in consts {
                if let Some(expr) = &cdef.expr {
                    let qname = format!("{}_{}", spec_name, cdef.name);
                    let v0 = format!("{}_0", qname);
                    let rhs = self.encode_const_expr(expr, true);
                    self.declare(&v0, "Bool");
                    self.assert_smt(&format!("(= {} {})", v0, rhs));
                }
            }
        }
    }

    /// Encode a boolean constant expression, creating intermediates for
    /// negation (`_neg`) and AND sub-expressions within OR.
    /// `toplevel` = true means the result goes directly into the const variable
    /// (no intermediate for the outermost AND).
    fn encode_const_expr(&mut self, expr: &Expr, toplevel: bool) -> String {
        match expr {
            Expr::Var(name) => {
                let qname = self.resolve_const_name(name);
                format!("{}_0", qname)
            }
            Expr::UnOp {
                op: UnOp::Not,
                expr: inner,
            } => {
                if let Expr::Var(name) = inner.as_ref() {
                    let base_q = self.resolve_const_name(name);
                    let neg_name = format!("{}_neg", base_q);
                    let neg_v0 = format!("{}_0", neg_name);
                    self.declare(&neg_v0, "Bool");
                    self.assert_smt(&format!("(= {} (not {}_0))", neg_v0, base_q));
                    neg_v0
                } else {
                    let inner_smt = self.encode_const_expr(inner, false);
                    format!("(not {})", inner_smt)
                }
            }
            Expr::BinOp {
                op: BinOp::And,
                left,
                right,
            } => {
                let l = self.encode_const_expr(left, false);
                let r = self.encode_const_expr(right, false);
                if toplevel {
                    // Top-level AND: encode inline, Go reverses operand order
                    format!("(and {} {})", r, l)
                } else {
                    // Nested AND (inside OR): create intermediate variable
                    let l_base = self.const_expr_base_name(left);
                    let r_base = self.const_expr_base_name(right);
                    let int_name = format!("{}_{}", l_base, r_base);
                    let int_v0 = format!("{}_0", int_name);
                    self.declare(&int_v0, "Bool");
                    self.assert_smt(&format!("(= {} (and {} {}))", int_v0, l, r));
                    int_v0
                }
            }
            Expr::BinOp {
                op: BinOp::Or,
                left,
                right,
            } => {
                // Go processes right sub-tree first, then reverses OR operand order
                let r = self.encode_const_expr(right, false);
                let l = self.encode_const_expr(left, false);
                format!("(or {} {})", r, l)
            }
            Expr::Lit(Val::Bool(b)) => if *b { "true" } else { "false" }.to_string(),
            _ => "false".to_string(),
        }
    }

    /// Resolve a constant name to its qualified form.
    fn resolve_const_name(&self, name: &str) -> String {
        self.name_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| format!("{}_{}", self.spec_name, name))
    }

    /// Get the qualified base name of a const expression (for AND intermediates).
    fn const_expr_base_name(&self, expr: &Expr) -> String {
        match expr {
            Expr::Var(name) => self.resolve_const_name(name),
            Expr::UnOp {
                op: UnOp::Not,
                expr: inner,
            } => {
                if let Expr::Var(name) = inner.as_ref() {
                    format!("{}_neg", self.resolve_const_name(name))
                } else {
                    self.const_expr_base_name(inner)
                }
            }
            _ => "tmp".to_string(),
        }
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
        let mut entry = BTreeMap::new();
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
            Stmt::Stay | Stmt::Advance(_)
            | Stmt::CompoundTransition(_) | Stmt::ChooseTransition(_) => {}
        }
    }

    /// Collect modified vars, resolving Call stmts through flow function bodies.
    fn collect_modified_vars_deep(&self, stmts: &[Stmt]) -> Vec<String> {
        let mut vars = Vec::new();
        for stmt in stmts {
            self.collect_modified_deep(stmt, &mut vars);
        }
        vars
    }

    fn collect_modified_deep(&self, stmt: &Stmt, vars: &mut Vec<String>) {
        match stmt {
            Stmt::FlowAssign { name, .. } => {
                if !vars.contains(name) {
                    vars.push(name.clone());
                }
            }
            Stmt::Call(call_name) => {
                if let Some(dot_pos) = call_name.rfind('.') {
                    let instance = &call_name[..dot_pos];
                    let func_name = &call_name[dot_pos + 1..];
                    if let Some(flow_type) = self.instances.get(instance)
                        && let Some(funcs) = self.flow_funcs.get(flow_type)
                        && let Some((_, body)) = funcs.iter().find(|(n, _)| n == func_name)
                    {
                        for s in body {
                            let resolved = self.resolve_flow_stmt(s, instance);
                            self.collect_modified_deep(&resolved, vars);
                        }
                    }
                }
            }
            Stmt::IfThenElse { then_branch, else_branch, .. } => {
                for s in then_branch {
                    self.collect_modified_deep(s, vars);
                }
                for s in else_branch {
                    self.collect_modified_deep(s, vars);
                }
            }
            Stmt::Seq(stmts) | Stmt::Parallel(stmts) => {
                for s in stmts {
                    self.collect_modified_deep(s, vars);
                }
            }
            _ => {}
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
        // Check name_map for instance-level resolution (handles target swaps)
        let local = self.qualify_local(name, instance);
        if let Some(qname) = self.name_map.get(&local) {
            return qname.clone();
        }
        format!("{}_{}", self.spec_name, local)
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
            Expr::Index { name, index } => Expr::Index {
                name: self.qualify_var(name, instance),
                index: *index,
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
        // If the name is already tracked in SSA, use it directly.
        // Otherwise, try with spec_name prefix (for run-block references
        // like "cluster_p_instances" → "orchestrator_cluster_p_instances").
        let effective = if self.ssa.has(name) {
            name.to_string()
        } else {
            let qualified = format!("{}_{}", self.spec_name, name);
            if self.ssa.has(&qualified) {
                qualified
            } else {
                name.to_string()
            }
        };
        if let Some(ref mut rssa) = self.read_ssa {
            rssa.current_name(&effective)
        } else {
            self.ssa.current_name(&effective)
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

        // Sync read_ssa to see this write for subsequent reads in same branch
        if let Some(ref mut rssa) = self.read_ssa {
            let ver = self.ssa.current(name);
            rssa.set_version(name, ver);
        }
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
            Expr::Index { name, index } => {
                // Absolute index: x[0] always refers to version at round `index`.
                // round_entries[0] = initial, round_entries[1] = after round 0, etc.
                let idx = *index as usize;
                if idx < self.round_entries.len()
                    && let Some(ver) = self.round_entries[idx].get(name)
                {
                    return ver.clone();
                }
                format!("{}_{}", name, index)
            }
            Expr::Dot { .. } => {
                // Flatten Dot chain to a qualified variable name, prepend spec_name.
                let parts = flatten_dot_chain(expr);
                let flat = parts.join("_");
                let qname = format!("{}_{}", self.spec_name, flat);
                self.read_current(&qname)
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

        let then_modified = self.collect_modified_vars_deep(then_branch);
        let else_modified = self.collect_modified_vars_deep(else_branch);

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

        // Block tracking booleans — same ID for true/false (matches Go oracle)
        self.block_counter += 1;
        let block_id = self.block_counter;

        let round_num = self.round_entries.len();
        let true_name = format!("block{}true_{}", block_id, round_num);
        let false_name = format!("block{}false_{}", block_id, round_num);
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
                "(or (and {} (not {})) (and (not {}) {}))",
                true_name, false_name, true_name, false_name
            ));
        }
    }

    /// Encode parallel execution with nondeterministic ordering.
    ///
    /// For 2 parallel calls [a, b], generates:
    /// - Perm 0: a then b → @__run_0 = (merge vars = perm0 results)
    /// - Perm 1: b then a → @__run_1 = (and (merge = perm0) (merge = perm1))
    /// - XOR: exactly one ordering selected
    fn encode_parallel(&mut self, stmts: &[Stmt], prog: &ResolvedProgram) {
        if stmts.len() < 2 {
            for s in stmts {
                self.encode_stmt(s, prog);
            }
            return;
        }

        let start_snap = self.ssa.snapshot();

        // Collect all variables that might be touched
        let tracked_vars: Vec<String> = self.all_vars.clone();

        // ── Perm 0: canonical order ────────────────────────────────────
        for s in stmts {
            self.encode_stmt(s, prog);
        }
        let perm0_snap = self.ssa.snapshot();

        // Collect perm0 final versioned names for tracked vars
        let perm0_finals: Vec<(String, String)> = tracked_vars
            .iter()
            .filter_map(|v: &String| {
                let start_v = start_snap.get(v).copied().unwrap_or(0);
                let end_v = perm0_snap.get(v).copied().unwrap_or(0);
                if end_v > start_v {
                    Some((v.clone(), format!("{}_{}", v, end_v)))
                } else {
                    None
                }
            })
            .collect();

        // Allocate merge variables for perm 0
        self.ssa.restore(perm0_snap.clone());
        let mut merge0: Vec<(String, String)> = Vec::new();
        for (base, _final_name) in &perm0_finals {
            let merge_name = self.ssa.next_name(base);
            let sort = self.sort_for(base);
            self.declare(&merge_name, sort);
            merge0.push((base.to_string(), merge_name));
        }
        let after_merge0_snap = self.ssa.snapshot();

        // Declare @__run selector variables
        self.declare("@__run_0", "Bool");
        self.declare("@__run_1", "Bool");

        // @__run_0 = (and (= merge_i perm0_final_i) ...)
        let perm0_eqs: Vec<String> = merge0
            .iter()
            .zip(perm0_finals.iter())
            .map(|((_, merge), (_, final_v))| format!("(= {} {})", merge, final_v))
            .collect();
        let run0_body = if perm0_eqs.len() == 1 {
            perm0_eqs[0].clone()
        } else {
            smt_and(&perm0_eqs)
        };
        self.assertions
            .push(format!("(assert (= @__run_0 {}))", run0_body));

        // ── Perm 1: reverse order ──────────────────────────────────────
        // Reads start from the original state, writes get fresh versions
        let mut read_ssa_for_perm1 = Ssa::new();
        read_ssa_for_perm1.restore(start_snap.clone());
        self.read_ssa = Some(read_ssa_for_perm1);
        // Main SSA continues from after merge0 for fresh write versions
        self.ssa.restore(after_merge0_snap.clone());

        for s in stmts.iter().rev() {
            self.encode_stmt(s, prog);
        }
        self.read_ssa = None;
        let perm1_snap = self.ssa.snapshot();

        // Collect perm1 final versioned names
        let perm1_finals: Vec<(String, String)> = tracked_vars
            .iter()
            .filter_map(|v: &String| {
                let after_m0 = after_merge0_snap.get(v).copied().unwrap_or(0);
                let end_v = perm1_snap.get(v).copied().unwrap_or(0);
                if end_v > after_m0 {
                    Some((v.clone(), format!("{}_{}", v, end_v)))
                } else {
                    None
                }
            })
            .collect();

        // Allocate merge variables for perm 1
        let mut merge1: Vec<(String, String)> = Vec::new();
        for (base, _) in &perm0_finals {
            let merge_name = self.ssa.next_name(base);
            let sort = self.sort_for(base);
            self.declare(&merge_name, sort);
            merge1.push((base.to_string(), merge_name));
        }

        // @__run_1 = (and (merge = perm0_final) (merge = perm1_final))
        let mut perm1_eqs_p0: Vec<String> = Vec::new();
        let mut perm1_eqs_p1: Vec<String> = Vec::new();
        for ((base, merge_name), (_, p0_final)) in merge1.iter().zip(perm0_finals.iter()) {
            perm1_eqs_p0.push(format!("(= {} {})", merge_name, p0_final));
            // Find perm1 final for this var
            if let Some((_, p1_final)) = perm1_finals.iter().find(|(b, _)| b == base) {
                perm1_eqs_p1.push(format!("(= {} {})", merge_name, p1_final));
            }
        }
        let group_p0 = smt_and(&perm1_eqs_p0);
        let group_p1 = smt_and(&perm1_eqs_p1);
        let run1_body = format!("(and {} {})", group_p0, group_p1);
        self.assertions
            .push(format!("(assert (= @__run_1 {}))", run1_body));

        // XOR constraint
        self.assertions.push(
            "(assert (or (and @__run_0 (not @__run_1)) (and (not @__run_0) @__run_1)))".into(),
        );
    }

    /// Encode invariants (assertions and assumptions).
    /// Go compiler emits assertions (negated) first, then assumptions.
    fn encode_invariants(&mut self, prog: &ResolvedProgram) {
        let num_rounds = prog.rounds;

        // First pass: assertions (negated for counterexample search)
        for inv in &prog.invariants {
            match inv {
                Invariant::Assert { expr, temporal } => {
                    let negated = self.encode_temporal_negated(expr, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", negated));
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
                _ => {}
            }
        }

        // Second pass: assumptions
        for inv in &prog.invariants {
            match inv {
                Invariant::Assume { expr, temporal } => {
                    let assumed = self.encode_temporal(expr, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", assumed));
                }
                Invariant::AssumeWhen {
                    guard,
                    body,
                    temporal,
                } => {
                    let assumed = self.encode_when_temporal(guard, body, temporal, num_rounds);
                    self.assertions.push(format!("(assert {})", assumed));
                }
                _ => {}
            }
        }
    }

    /// Encode a temporal property (not negated, for assumptions).
    fn encode_temporal(&self, expr: &Expr, temporal: &Temporal, num_rounds: u64) -> String {
        let round_exprs: Vec<String> = (0..=num_rounds)
            .map(|r| self.encode_expr_at_round(expr, r))
            .collect();

        match temporal {
            Temporal::Always => smt_and(&round_exprs),
            Temporal::Eventually => smt_or(&round_exprs),
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
                let negated: Vec<String> = round_exprs.iter().map(|e| negate_smt_expr(e)).collect();
                smt_or(&negated)
            }
            Temporal::Eventually => {
                let negated: Vec<String> = round_exprs.iter().map(|e| negate_smt_expr(e)).collect();
                smt_and(&negated)
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
                // Try spec-qualified variant if unresolved
                let effective = if self.ssa.has(&resolved) {
                    resolved
                } else {
                    let qualified = format!("{}_{}", self.spec_name, resolved);
                    if self.ssa.has(&qualified) {
                        qualified
                    } else {
                        resolved
                    }
                };
                // Use round_entries if available; constants (never assigned)
                // always stay at version 0.
                let ridx = round as usize;
                if ridx < self.round_entries.len() {
                    if let Some(ver) = self.round_entries[ridx].get(&effective) {
                        return ver.clone();
                    }
                }
                // Fallback: constant or untracked → version 0
                format!("{}_0", effective)
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

    // ── Mixed system (statechart + flows) helpers ─────────────────────

    /// Encode a state function body with an outer ite guard.
    fn encode_state_func(
        &mut self,
        comp: &str,
        state: &str,
        body: &[Stmt],
        prog: &ResolvedProgram,
        spec_name: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
    ) {
        let state_qname = format!("{}_{}_{}", spec_name, comp, state);
        let guard_ver = self.ssa.current(&state_qname);
        let guard_var = format!("{}_{}", state_qname, guard_ver);

        // Handle stay() — bump state var, set true, wrap in state-active ite
        if body.len() == 1 && matches!(&body[0], Stmt::Stay) {
            let pre_ver = self.ssa.current(&state_qname);
            let new_ver = self.ssa.bump(&state_qname);
            let new_vname = format!("{}_{}", state_qname, new_ver);
            self.declare(&new_vname, "Bool");
            self.assert_smt(&format!("(= {} true)", new_vname));
            self.emit_state_active_ite(&guard_var, &state_qname, new_ver, pre_ver);
            return;
        }

        // Snapshot pre-body SSA versions for all tracked variables
        let pre_flow: BTreeMap<String, u32> = self
            .all_vars
            .iter()
            .map(|v| (v.clone(), self.ssa.current(v)))
            .collect();

        // Encode body
        let pre_assert_count = self.assertions.len();
        for stmt in body {
            self.encode_mixed_stmt_in_state(stmt, prog, spec_name, comp, comp_states, &guard_var);
        }

        if self.assertions.len() == pre_assert_count {
            return; // body produced nothing
        }

        // Collect flow vars that changed — they need an outer state-active ite guard
        // (but only those not already wrapped by inner ite guards from conditionals)
        let mut changed: Vec<String> = Vec::new();
        for v in &self.all_vars {
            if self.ssa.current(v) != pre_flow.get(v).copied().unwrap_or(0) {
                changed.push(v.clone());
            }
        }

        // If the body was just a bare Call (no conditional), wrap the changed
        // vars in a state-active ite guard.
        if body.len() == 1 && matches!(&body[0], Stmt::Call(_)) && !changed.is_empty() {
            self.block_counter += 1;
            let block_id = self.block_counter;
            let bt = format!("block{}true_0", block_id);
            let bf = format!("block{}false_0", block_id);
            self.declare(&bt, "Bool");
            self.declare(&bf, "Bool");

            let mut true_eqs = vec![
                format!("(= {} true)", bt),
                format!("(= {} false)", bf),
            ];
            let mut false_eqs = vec![
                format!("(= {} false)", bt),
                format!("(= {} true)", bf),
            ];

            for v in &changed {
                let post = self.ssa.current(v);
                let pre = pre_flow[v];
                let nv = self.ssa.bump(v);
                let result_name = format!("{}_{}", v, nv);
                let sort = self.var_sorts.get(v).copied().unwrap_or("Real");
                self.declare(&result_name, sort);
                true_eqs.push(format!("(= {} {}_{})", result_name, v, post));
                false_eqs.push(format!("(= {} {}_{})", result_name, v, pre));
            }

            let guard = format!("(= {} true)", guard_var);
            self.assert_smt(&format!(
                "(ite {} (and {}) (and {}))",
                guard,
                true_eqs.join(" "),
                false_eqs.join(" ")
            ));
            self.assertions.push(format!(
                "(assert (or (and {}\n(not {}))\n(and (not {})\n{})))",
                bt, bf, bt, bf
            ));
        }
    }

    /// Encode a statement inside a state function body.
    fn encode_mixed_stmt_in_state(
        &mut self,
        stmt: &Stmt,
        prog: &ResolvedProgram,
        spec_name: &str,
        comp: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
        guard_var: &str,
    ) {
        match stmt {
            Stmt::Call(name) => self.encode_call(name, prog),
            Stmt::FlowAssign { name, op, expr } => self.encode_flow_assign(name, *op, expr),
            Stmt::IfThenElse { cond, then_branch, else_branch } => {
                self.encode_mixed_if_in_state(
                    cond, then_branch, else_branch, prog, spec_name, comp, comp_states, guard_var,
                );
            }
            Stmt::Advance(target) => {
                let target_name = target.strip_prefix("this.").unwrap_or(target);
                let target_qname = format!("{}_{}_{}", spec_name, comp, target_name);
                let v = self.ssa.bump(&target_qname);
                let vname = format!("{}_{}", target_qname, v);
                self.declare(&vname, "Bool");
                self.assert_smt(&format!("(= {} true)", vname));
            }
            Stmt::Stay => {}
            Stmt::Seq(stmts) => {
                for s in stmts {
                    self.encode_mixed_stmt_in_state(s, prog, spec_name, comp, comp_states, guard_var);
                }
            }
            _ => {}
        }
    }

    /// Encode an if-then-else inside a state function.
    ///
    /// Pattern from Go oracle:
    /// - `if cond { fn }` → combined (state AND cond) guard
    /// - `if cond { advance } else { fn }` → fn gets state-only guard, advance gets combined
    fn encode_mixed_if_in_state(
        &mut self,
        cond: &Expr,
        then_branch: &[Stmt],
        else_branch: &[Stmt],
        prog: &ResolvedProgram,
        spec_name: &str,
        comp: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
        guard_var: &str,
    ) {
        let then_has_flow = branches_have_flow(then_branch);
        let else_has_flow = branches_have_flow(else_branch);
        let then_has_advance = branches_have_advance(then_branch);

        // Snapshot pre-body versions
        let pre_body_versions: BTreeMap<String, u32> = self
            .all_vars
            .iter()
            .map(|v| (v.clone(), self.ssa.current(v)))
            .collect();

        // Determine which flow branch to encode and what guard to use
        if then_has_flow && !else_has_flow {
            // `if cond { fn }` — combined guard
            for s in then_branch {
                match s {
                    Stmt::Call(name) => self.encode_call(name, prog),
                    Stmt::FlowAssign { name, op, expr } => self.encode_flow_assign(name, *op, expr),
                    _ => {}
                }
            }
            let cond_smt = self.encode_mixed_expr(cond, spec_name, comp_states);
            let guard = format!("(and (= {} true) {})", guard_var, cond_smt);
            self.emit_flow_ite_guard(&guard, &pre_body_versions);
        } else if else_has_flow {
            // `if cond { ... } else { fn }` or `if cond { fn } else { fn }`
            // Encode else-branch flow, use state-only guard (matching Go behavior)
            for s in else_branch {
                match s {
                    Stmt::Call(name) => self.encode_call(name, prog),
                    Stmt::FlowAssign { name, op, expr } => self.encode_flow_assign(name, *op, expr),
                    _ => {}
                }
            }
            let guard = format!("(= {} true)", guard_var);
            self.emit_flow_ite_guard(&guard, &pre_body_versions);

            // If then also has flow, encode it with combined guard
            if then_has_flow {
                let pre2: BTreeMap<String, u32> = self
                    .all_vars
                    .iter()
                    .map(|v| (v.clone(), self.ssa.current(v)))
                    .collect();
                for s in then_branch {
                    match s {
                        Stmt::Call(name) => self.encode_call(name, prog),
                        Stmt::FlowAssign { name, op, expr } => self.encode_flow_assign(name, *op, expr),
                        _ => {}
                    }
                }
                let cond_smt = self.encode_mixed_expr(cond, spec_name, comp_states);
                let guard = format!("(and (= {} true) {})", guard_var, cond_smt);
                self.emit_flow_ite_guard(&guard, &pre2);
            }
        }

        // Handle advance in then branch
        if then_has_advance {
            for s in then_branch {
                if let Stmt::Advance(target) = s {
                    let target_name = target.strip_prefix("this.").unwrap_or(target);
                    let target_qname = format!("{}_{}_{}", spec_name, comp, target_name);
                    let pre_ver = self.ssa.current(&target_qname);
                    let v = self.ssa.bump(&target_qname);
                    let vname = format!("{}_{}", target_qname, v);
                    self.declare(&vname, "Bool");
                    self.assert_smt(&format!("(= {} true)", vname));

                    let cond_smt = self.encode_mixed_expr(cond, spec_name, comp_states);
                    let combined = format!("(and (= {} true) {})", guard_var, cond_smt);
                    self.emit_advance_ite_guard(&combined, &target_qname, &vname, pre_ver);
                }
            }
        }

        // Handle advance in else branch
        let else_has_advance = branches_have_advance(else_branch);
        if else_has_advance {
            for s in else_branch {
                if let Stmt::Advance(target) = s {
                    let target_name = target.strip_prefix("this.").unwrap_or(target);
                    let target_qname = format!("{}_{}_{}", spec_name, comp, target_name);
                    let pre_ver = self.ssa.current(&target_qname);
                    let v = self.ssa.bump(&target_qname);
                    let vname = format!("{}_{}", target_qname, v);
                    self.declare(&vname, "Bool");
                    self.assert_smt(&format!("(= {} true)", vname));

                    let cond_smt = self.encode_mixed_expr(cond, spec_name, comp_states);
                    let combined = format!("(and (= {} true) (not {}))", guard_var, cond_smt);
                    self.emit_advance_ite_guard(&combined, &target_qname, &vname, pre_ver);
                }
            }
        }
    }

    /// Emit an ite guard for flow variable changes.
    fn emit_flow_ite_guard(
        &mut self,
        guard: &str,
        pre_versions: &BTreeMap<String, u32>,
    ) {
        let mut changed: Vec<String> = Vec::new();
        for v in &self.all_vars {
            if self.ssa.current(v) != pre_versions.get(v).copied().unwrap_or(0) {
                changed.push(v.clone());
            }
        }

        if changed.is_empty() {
            return;
        }

        self.block_counter += 1;
        let block_id = self.block_counter;
        let bt = format!("block{}true_0", block_id);
        let bf = format!("block{}false_0", block_id);
        self.declare(&bt, "Bool");
        self.declare(&bf, "Bool");

        let mut true_eqs = vec![format!("(= {} true)", bt), format!("(= {} false)", bf)];
        let mut false_eqs = vec![format!("(= {} false)", bt), format!("(= {} true)", bf)];

        for v in &changed {
            let post = self.ssa.current(v);
            let pre = pre_versions[v];
            let nv = self.ssa.bump(v);
            let result_name = format!("{}_{}", v, nv);
            let sort = self.var_sorts.get(v).copied().unwrap_or("Real");
            self.declare(&result_name, sort);
            true_eqs.push(format!("(= {} {}_{})", result_name, v, post));
            false_eqs.push(format!("(= {} {}_{})", result_name, v, pre));
        }

        self.assert_smt(&format!(
            "(ite {} (and {}) (and {}))",
            guard,
            true_eqs.join(" "),
            false_eqs.join(" ")
        ));
        self.assertions.push(format!(
            "(assert (or (and {}\n(not {}))\n(and (not {})\n{})))",
            bt, bf, bt, bf
        ));
    }

    /// Emit an ite guard for an advance (state Bool variable change).
    fn emit_advance_ite_guard(
        &mut self,
        guard: &str,
        target_qname: &str,
        advance_vname: &str,
        pre_ver: u32,
    ) {
        self.block_counter += 1;
        let block_id = self.block_counter;
        let bt = format!("block{}true_0", block_id);
        let bf = format!("block{}false_0", block_id);
        self.declare(&bt, "Bool");
        self.declare(&bf, "Bool");

        let rv = self.ssa.bump(target_qname);
        let result_name = format!("{}_{}", target_qname, rv);
        self.declare(&result_name, "Bool");

        self.assert_smt(&format!(
            "(ite {} (and (= {} true) (= {} false) (= {} {})) \
             (and (= {} false) (= {} true) (= {} {}_{})))",
            guard,
            bt, bf, result_name, advance_vname,
            bt, bf, result_name, target_qname, pre_ver
        ));
        self.assertions.push(format!(
            "(assert (or (and {}\n(not {}))\n(and (not {})\n{})))",
            bt, bf, bt, bf
        ));
    }

    /// Emit a state-active ite guard for a single variable (used by stay/advance).
    fn emit_state_active_ite(
        &mut self,
        guard_var: &str,
        target_qname: &str,
        new_ver: u32,
        pre_ver: u32,
    ) {
        let new_vname = format!("{}_{}", target_qname, new_ver);
        let guard = format!("(= {} true)", guard_var);
        self.emit_advance_ite_guard(&guard, target_qname, &new_vname, pre_ver);
    }

    /// Encode a statement in a mixed system run block.
    fn encode_mixed_stmt(
        &mut self,
        stmt: &Stmt,
        prog: &ResolvedProgram,
        spec_name: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
    ) {
        match stmt {
            Stmt::Call(name) => self.encode_call(name, prog),
            Stmt::IfThenElse { cond, then_branch, else_branch } => {
                self.encode_mixed_run_if(cond, then_branch, else_branch, prog, spec_name, comp_states);
            }
            Stmt::Seq(stmts) => {
                for s in stmts {
                    self.encode_mixed_stmt(s, prog, spec_name, comp_states);
                }
            }
            _ => self.encode_stmt(stmt, prog),
        }
    }

    /// Encode an if-then-else in a run block that may reference state variables.
    fn encode_mixed_run_if(
        &mut self,
        cond: &Expr,
        then_branch: &[Stmt],
        _else_branch: &[Stmt],
        prog: &ResolvedProgram,
        spec_name: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
    ) {
        let pre_versions: BTreeMap<String, u32> = self
            .all_vars
            .iter()
            .map(|v| (v.clone(), self.ssa.current(v)))
            .collect();

        for s in then_branch {
            self.encode_stmt(s, prog);
        }

        let mut changed: Vec<String> = Vec::new();
        for v in &self.all_vars {
            if self.ssa.current(v) != pre_versions.get(v).copied().unwrap_or(0) {
                changed.push(v.clone());
            }
        }

        if changed.is_empty() {
            return;
        }

        let cond_smt = self.encode_mixed_expr(cond, spec_name, comp_states);

        let block_id = self.block_counter;
        self.block_counter += 1;
        let bt = format!("block{}true_0", block_id);
        let bf = format!("block{}false_0", block_id);
        self.declare(&bt, "Bool");
        self.declare(&bf, "Bool");

        let mut true_eqs = vec![format!("(= {} true)", bt), format!("(= {} false)", bf)];
        let mut false_eqs = vec![format!("(= {} false)", bt), format!("(= {} true)", bf)];

        for v in &changed {
            let post = self.ssa.current(v);
            let pre = pre_versions[v];
            let nv = self.ssa.bump(v);
            let result_name = format!("{}_{}", v, nv);
            let sort = self.var_sorts.get(v).copied().unwrap_or("Real");
            self.declare(&result_name, sort);
            true_eqs.push(format!("(= {} {}_{})", result_name, v, post));
            false_eqs.push(format!("(= {} {}_{})", result_name, v, pre));
        }

        self.assert_smt(&format!(
            "(ite {} (and {}) (and {}))",
            cond_smt,
            true_eqs.join(" "),
            false_eqs.join(" ")
        ));
        self.assertions.push(format!(
            "(assert (or (and {}\n(not {}))\n(and (not {})\n{})))",
            bt, bf, bt, bf
        ));
    }

    /// Encode an expression that may reference state variables or flow properties.
    fn encode_mixed_expr(
        &mut self,
        expr: &Expr,
        spec_name: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
    ) -> String {
        match expr {
            Expr::Lit(val) => val_to_smt(val),
            Expr::UnOp { op: UnOp::Not, expr: inner } => {
                let inner_smt = self.encode_mixed_expr_bare(inner, spec_name, comp_states);
                format!("(not {})", inner_smt)
            }
            Expr::BinOp { op, left, right } => {
                let l = self.encode_mixed_expr(left, spec_name, comp_states);
                let r = self.encode_mixed_expr(right, spec_name, comp_states);
                format!("({} {} {})", binop_to_smt(*op), l, r)
            }
            Expr::Dot { .. } => {
                // Flatten dot chain to parts: fl.vault.value → ["fl", "vault", "value"]
                let parts = flatten_dot_chain(expr);
                if !parts.is_empty() {
                    let first = &parts[0];
                    // Component state reference: drain.close
                    if parts.len() == 2 {
                        if let Some(states) = comp_states.get(first.as_str()) {
                            if states.contains(&parts[1]) {
                                let qname = format!("{}_{}_{}", spec_name, first, parts[1]);
                                let ver = self.ssa.current(&qname);
                                return format!("{}_{}", qname, ver);
                            }
                        }
                    }
                    // Flow instance property reference (fl.active, fl.vault.value)
                    if self.instances.contains_key(first.as_str()) {
                        let rest = parts[1..].join("_");
                        // Try name_map with just the property part
                        if let Some(qname) = self.name_map.get(&rest).cloned() {
                            return self.mixed_var_versioned(&qname);
                        }
                        // Try with instance+rest
                        let inst_rest = format!("{}_{}", first, rest);
                        if let Some(qname) = self.name_map.get(&inst_rest).cloned() {
                            return self.mixed_var_versioned(&qname);
                        }
                        // Construct directly
                        let qname = format!("{}_{}", spec_name, inst_rest);
                        return self.mixed_var_versioned(&qname);
                    }
                }
                self.encode_expr(expr)
            }
            Expr::Var(name) => {
                // Check if flattened name matches comp_state (from resolution)
                for (comp_name, states) in comp_states {
                    let prefix = format!("{}_", comp_name);
                    if let Some(state) = name.strip_prefix(&prefix) {
                        if states.contains(&state.to_string()) {
                            let qname = format!("{}_{}_{}", spec_name, comp_name, state);
                            let ver = self.ssa.current(&qname);
                            return format!("{}_{}", qname, ver);
                        }
                    }
                }
                // Check if name matches a name_map key (flattened flow property)
                if let Some(qname) = self.name_map.get(name.as_str()).cloned() {
                    return self.mixed_var_versioned(&qname);
                }
                self.encode_expr(expr)
            }
            _ => self.encode_expr(expr),
        }
    }

    /// Like `encode_mixed_expr` but doesn't wrap Bool vars in `(= x true)`.
    /// Used inside `not` context where wrapping is redundant.
    fn encode_mixed_expr_bare(
        &mut self,
        expr: &Expr,
        spec_name: &str,
        comp_states: &BTreeMap<String, Vec<String>>,
    ) -> String {
        // For Dot chains that resolve to a qualified var, return bare name
        if let Expr::Dot { .. } = expr {
            let parts = flatten_dot_chain(expr);
            if !parts.is_empty() {
                let first = &parts[0];
                if parts.len() == 2 {
                    if let Some(states) = comp_states.get(first.as_str()) {
                        if states.contains(&parts[1]) {
                            let qname = format!("{}_{}_{}", spec_name, first, parts[1]);
                            let ver = self.ssa.current(&qname);
                            return format!("{}_{}", qname, ver);
                        }
                    }
                }
                if self.instances.contains_key(first.as_str()) {
                    let rest = parts[1..].join("_");
                    if let Some(qname) = self.name_map.get(&rest).cloned() {
                        let ver = self.ssa.current(&qname);
                        return format!("{}_{}", qname, ver);
                    }
                    let inst_rest = format!("{}_{}", first, rest);
                    if let Some(qname) = self.name_map.get(&inst_rest).cloned() {
                        let ver = self.ssa.current(&qname);
                        return format!("{}_{}", qname, ver);
                    }
                }
            }
        }
        if let Expr::Var(name) = expr {
            for (comp_name, states) in comp_states {
                let prefix = format!("{}_", comp_name);
                if let Some(state) = name.strip_prefix(&prefix) {
                    if states.contains(&state.to_string()) {
                        let qname = format!("{}_{}_{}", spec_name, comp_name, state);
                        let ver = self.ssa.current(&qname);
                        return format!("{}_{}", qname, ver);
                    }
                }
            }
        }
        // Fall back to normal encoding (includes wrapping for non-bare contexts)
        self.encode_mixed_expr(expr, spec_name, comp_states)
    }

    /// Return a versioned variable name, wrapping Bool vars in `(= ... true)`.
    fn mixed_var_versioned(&mut self, qname: &str) -> String {
        let ver = self.ssa.current(qname);
        let vname = format!("{}_{}", qname, ver);
        if self.var_sorts.get(qname).copied() == Some("Bool") {
            format!("(= {} true)", vname)
        } else {
            vname
        }
    }

    /// Produce the final SMT-LIB2 string.
    /// Remove declarations and assertions for flow properties not in the referenced set.
    fn filter_unreferenced_vars(&mut self, referenced: &HashSet<String>, _spec_name: &str) {
        // Build set of qualified names to keep: those whose short name matches a reference
        let mut to_remove: Vec<String> = Vec::new();
        for (short, qname) in &self.name_map {
            // Check if any suffix of the short name is in referenced
            let is_ref = referenced.contains(short)
                || short.split('_').last().map_or(false, |leaf| referenced.contains(leaf));
            if !is_ref {
                to_remove.push(qname.clone());
            }
        }

        if to_remove.is_empty() {
            return;
        }

        // Remove declarations for these qualified names
        self.declarations.retain(|(name, _)| {
            !to_remove.iter().any(|r| name.starts_with(r))
        });
        // Remove assertions referencing these
        self.assertions.retain(|a| {
            !to_remove.iter().any(|r| a.contains(r))
        });
        // Remove from declared set
        for r in &to_remove {
            self.declared.retain(|d| !d.starts_with(r));
        }
    }

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
    if !prog.components.is_empty() {
        if prog.stocks.is_empty() && prog.flows.is_empty() {
            return encode_statechart_only(prog, spec_name);
        }
        return encode_mixed_system(prog, spec_name);
    }

    let mut w = SmtWriter::new(spec_name);
    w.build_mappings(prog);
    w.encode_constants(prog);
    w.encode_initial_values();

    for _ in 0..prog.rounds {
        w.encode_round(prog);
    }

    w.encode_invariants(prog);
    w.emit()
}

/// Encode a system with both components (statechart) and imported flows.
fn encode_mixed_system(prog: &ResolvedProgram, spec_name: &str) -> String {
    let mut w = SmtWriter::new(spec_name);
    w.build_mappings(prog);
    w.encode_constants(prog);
    w.encode_initial_values();
    // Remove the round entry snapshot from encode_initial_values so blocks use _0 suffix
    w.round_entries.clear();

    // Filter unreferenced stock sub-properties, but only when no flow function calls exist.
    // When any Call stmt exists (in components or run block), all stock properties may be needed.
    let has_flow_calls = prog.run_block.iter().any(|s| stmt_has_call(s))
        || prog.components.iter().any(|c| c.states.iter().any(|(_, body)| body.iter().any(|s| stmt_has_call(s))));
    if !has_flow_calls {
        let referenced = collect_referenced_flow_props(prog);
        w.filter_unreferenced_vars(&referenced, spec_name);
    }

    // Declare and initialize state Bool variables (version 0 = false)
    for comp in &prog.components {
        for (state_name, _) in &comp.states {
            let qname = format!("{}_{}_{}", spec_name, comp.name, state_name);
            let v0 = format!("{}_0", qname);
            w.declare(&v0, "Bool");
            w.assert_smt(&format!("(= {} false)", v0));
            // SSA starts at 0, don't bump yet
        }
    }

    // Set start states to true (bump to version 1)
    for (comp, start) in &prog.start_states {
        let qname = format!("{}_{}_{}", spec_name, comp, start);
        let v = w.ssa.bump(&qname);
        let vname = format!("{}_{}", qname, v);
        w.declare(&vname, "Bool");
        w.assert_smt(&format!("(= {} true)", vname));
    }

    // Build state name list per component
    let comp_states: BTreeMap<String, Vec<String>> = prog
        .components
        .iter()
        .map(|c| {
            let names: Vec<String> = c.states.iter().map(|(s, _)| s.clone()).collect();
            (c.name.clone(), names)
        })
        .collect();

    // Encode rounds
    let rounds = if prog.rounds == 0 { 1 } else { prog.rounds };
    for _ in 0..rounds {
        if !prog.run_block.is_empty() {
            for stmt in &prog.run_block {
                w.encode_mixed_stmt(stmt, prog, spec_name, &comp_states);
            }
        }

        // Determine if components use compound transitions (advance || / &&)
        let uses_compound = prog.components.iter().any(|c| {
            c.states.iter().any(|(_, body)| {
                body.iter().any(|s| matches!(s, Stmt::CompoundTransition(_) | Stmt::ChooseTransition(_)))
                    || body.iter().any(|s| stmt_contains_compound(s))
            })
        });

        if uses_compound {
            // Process flow function calls from state bodies through SmtWriter,
            // then delegate statechart transitions to StateChartEncoder.
            //
            // State bodies may contain Call("record.lookup") etc. that need
            // the flow encoder to inline the function body (stock variable
            // assignments). These must be processed per-state, in order,
            // so the SSA versions are correct for subsequent ITE guards.
            let mut stripped_components = Vec::new();
            for comp in &prog.components {
                let mut stripped_states = Vec::new();
                for (state_name, body) in &comp.states {
                    // Extract and process Call statements through SmtWriter
                    let state_qname = format!("{}_{}_{}", spec_name, comp.name, state_name);
                    let state_ver = w.ssa.current(&state_qname);
                    let state_guard = format!("{}_{}", state_qname, state_ver);

                    let calls: Vec<&Stmt> = body.iter().filter(|s| matches!(s, Stmt::Call(_))).collect();
                    let rest: Vec<Stmt> = body.iter().filter(|s| !matches!(s, Stmt::Call(_))).cloned().collect();

                    if !calls.is_empty() {
                        // Collect all stock vars modified by the calls
                        let pre_vars: BTreeMap<String, String> = w.all_vars.iter()
                            .map(|v| (v.clone(), w.ssa.current_name(v)))
                            .collect();

                        for call_stmt in &calls {
                            if let Stmt::Call(name) = call_stmt {
                                w.encode_call(name, prog);
                            }
                        }

                        // Find which stock vars were modified and gate them
                        let mut modified = Vec::new();
                        for (var, pre_name) in &pre_vars {
                            let post_name = w.ssa.current_name(var);
                            if post_name != *pre_name {
                                modified.push((var.clone(), pre_name.clone(), post_name));
                            }
                        }

                        // Emit ITE guard: if state active, keep flow effects; else carry forward
                        if !modified.is_empty() {
                            let block_id = w.block_counter;
                            w.block_counter += 1;
                            let bt = format!("block{}true_0", block_id);
                            let bf = format!("block{}false_0", block_id);
                            w.declare(&bt, "Bool");
                            w.declare(&bf, "Bool");

                            let mut true_parts = vec![
                                format!("(= {} true)", bt),
                                format!("(= {} false)", bf),
                            ];
                            let mut false_parts = vec![
                                format!("(= {} false)", bt),
                                format!("(= {} true)", bf),
                            ];

                            for (var, pre_name, post_name) in &modified {
                                true_parts.push(format!("(= {} {})", post_name, post_name));
                                // In false branch, create a carry-forward version
                                let carry_ver = w.ssa.bump(var);
                                let carry_name = format!("{}_{}", var, carry_ver);
                                let sort = w.var_sorts.get(var).copied().unwrap_or("Real");
                                w.declare(&carry_name, sort);
                                false_parts.push(format!("(= {} {})", carry_name, pre_name));
                            }

                            let ite = format!(
                                "(ite (= {} true) (and {}) (and {}))",
                                state_guard,
                                true_parts.join(" "),
                                false_parts.join(" "),
                            );
                            w.assert_smt(&ite);
                            w.assert_smt(&format!(
                                "(or (and {} (not {})) (and (not {}) {}))",
                                bt, bf, bt, bf
                            ));
                        }
                    }

                    stripped_states.push((state_name.clone(), rest));
                }
                stripped_components.push(CompDef {
                    name: comp.name.clone(),
                    states: stripped_states,
                });
            }

            // Pre-resolve conditions and delegate transitions to StateChartEncoder
            let resolved_comps = pre_resolve_components(
                &stripped_components, spec_name, &w,
            );
            let mut version_state: BTreeMap<String, u32> = BTreeMap::new();
            for comp in &prog.components {
                for (state_name, _) in &comp.states {
                    let qname = format!("{}_{}_{}", spec_name, comp.name, state_name);
                    version_state.insert(qname.clone(), w.ssa.current(&qname));
                }
            }
            let mut enc = crate::statechart::StateChartEncoder::new(spec_name);
            let (decls, asserts) = enc.encode_components_with_versions(&resolved_comps, &version_state);
            for d in &decls {
                // Parse declaration: (declare-fun NAME () SORT)
                if let Some(rest) = d.strip_prefix("(declare-fun ") {
                    if let Some(name_end) = rest.find(" ()") {
                        let name = rest[..name_end].to_string();
                        let sort_start = rest.find("() ").map(|i| i + 3).unwrap_or(0);
                        let sort_str = rest[sort_start..].trim_end_matches(')').trim();
                        let sort: &'static str = match sort_str {
                            "Bool" => "Bool",
                            _ => "Real",
                        };
                        w.declare(&name, sort);
                    }
                }
            }
            for a in &asserts {
                w.assertions.push(a.clone());
            }
        } else {
            for comp in &prog.components {
                for (state_name, body) in &comp.states {
                    w.encode_state_func(&comp.name, state_name, body, prog, spec_name, &comp_states);
                }
            }
        }
    }

    w.encode_invariants(prog);
    w.emit()
}

/// Encode a program that only has components (no stocks/flows).
fn encode_statechart_only(prog: &ResolvedProgram, spec_name: &str) -> String {
    let mut enc = crate::statechart::StateChartEncoder::new(spec_name);
    let (decls, asserts) = enc.encode(&prog.components, &prog.start_states);

    let mut out = String::new();
    out.push_str("(set-logic QF_NRA)\n");
    for d in &decls {
        out.push_str(d);
        out.push('\n');
    }
    for a in &asserts {
        out.push_str(a);
        out.push('\n');
    }
    out
}

// ── Helpers ─────────────────────────────────────────────────────────

/// Determine the SMT sort for a value.
/// Collect all flow property paths referenced in components and run block.
/// Returns a set of short names like "active", "vault_value".
fn collect_referenced_flow_props(prog: &ResolvedProgram) -> HashSet<String> {
    let mut refs = HashSet::new();
    for comp in &prog.components {
        for (_, body) in &comp.states {
            for stmt in body {
                collect_refs_in_stmt(stmt, &mut refs);
            }
        }
    }
    for stmt in &prog.run_block {
        collect_refs_in_stmt(stmt, &mut refs);
    }
    refs
}

fn collect_refs_in_stmt(stmt: &Stmt, refs: &mut HashSet<String>) {
    match stmt {
        Stmt::IfThenElse { cond, then_branch, else_branch } => {
            collect_refs_in_expr(cond, refs);
            for s in then_branch { collect_refs_in_stmt(s, refs); }
            for s in else_branch { collect_refs_in_stmt(s, refs); }
        }
        Stmt::Call(name) => { refs.insert(name.clone()); }
        Stmt::FlowAssign { name, expr, .. } => {
            collect_refs_in_expr(&Expr::Var(name.clone()), refs);
            collect_refs_in_expr(expr, refs);
        }
        Stmt::Seq(stmts) => { for s in stmts { collect_refs_in_stmt(s, refs); } }
        _ => {}
    }
}

fn collect_refs_in_expr(expr: &Expr, refs: &mut HashSet<String>) {
    match expr {
        Expr::Dot { expr: base, field: _ } => {
            let parts = flatten_dot_chain(expr);
            if parts.len() >= 2 {
                // Add the leaf property name and all intermediate paths
                refs.insert(parts[1..].join("_"));
                for i in 1..parts.len() {
                    refs.insert(parts[i..].join("_"));
                }
            }
            collect_refs_in_expr(base, refs);
        }
        Expr::UnOp { expr: inner, .. } => collect_refs_in_expr(inner, refs),
        Expr::BinOp { left, right, .. } => {
            collect_refs_in_expr(left, refs);
            collect_refs_in_expr(right, refs);
        }
        Expr::Var(name) => { refs.insert(name.clone()); }
        _ => {}
    }
}

/// Check if a statement (recursively) contains a flow function Call.
fn stmt_has_call(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Call(_) => true,
        Stmt::IfThenElse { then_branch, else_branch, .. } => {
            then_branch.iter().any(|s| stmt_has_call(s))
                || else_branch.iter().any(|s| stmt_has_call(s))
        }
        Stmt::Seq(stmts) => stmts.iter().any(|s| stmt_has_call(s)),
        _ => false,
    }
}

/// Check if a statement (recursively) contains CompoundTransition or ChooseTransition.
fn stmt_contains_compound(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::CompoundTransition(_) | Stmt::ChooseTransition(_) => true,
        Stmt::IfThenElse { then_branch, else_branch, .. } => {
            then_branch.iter().any(|s| stmt_contains_compound(s))
                || else_branch.iter().any(|s| stmt_contains_compound(s))
        }
        Stmt::Seq(stmts) => stmts.iter().any(|s| stmt_contains_compound(s)),
        _ => false,
    }
}

/// Pre-resolve flow variable references in component conditions.
/// Replaces `Dot(Var("fl"), "active")` with `Var("spec_fl_active_0")`.
fn pre_resolve_components(
    components: &[CompDef],
    spec_name: &str,
    w: &SmtWriter,
) -> Vec<CompDef> {
    components
        .iter()
        .map(|comp| CompDef {
            name: comp.name.clone(),
            states: comp
                .states
                .iter()
                .map(|(name, body)| {
                    let resolved = body
                        .iter()
                        .map(|s| pre_resolve_stmt(s, spec_name, w))
                        .collect();
                    (name.clone(), resolved)
                })
                .collect(),
        })
        .collect()
}

fn pre_resolve_stmt(stmt: &Stmt, spec_name: &str, w: &SmtWriter) -> Stmt {
    match stmt {
        Stmt::IfThenElse { cond, then_branch, else_branch } => Stmt::IfThenElse {
            cond: pre_resolve_expr(cond, spec_name, w),
            then_branch: then_branch.iter().map(|s| pre_resolve_stmt(s, spec_name, w)).collect(),
            else_branch: else_branch.iter().map(|s| pre_resolve_stmt(s, spec_name, w)).collect(),
        },
        Stmt::Seq(stmts) => Stmt::Seq(stmts.iter().map(|s| pre_resolve_stmt(s, spec_name, w)).collect()),
        _ => stmt.clone(),
    }
}

fn pre_resolve_expr(expr: &Expr, spec_name: &str, w: &SmtWriter) -> Expr {
    match expr {
        Expr::Dot { expr: base, field } => {
            let parts = flatten_dot_chain(expr);
            if !parts.is_empty() && w.instances.contains_key(parts[0].as_str()) {
                // Flow instance variable: resolve to qualified versioned name
                let rest = parts[1..].join("_");
                let inst_rest = format!("{}_{}", parts[0], rest);
                // Look up in name_map
                if let Some(qname) = w.name_map.get(&inst_rest) {
                    let ver = w.ssa.current_ro(qname);
                    return Expr::Var(format!("{}_{}", qname, ver));
                }
                if let Some(qname) = w.name_map.get(&rest) {
                    let ver = w.ssa.current_ro(qname);
                    return Expr::Var(format!("{}_{}", qname, ver));
                }
            }
            // Not a flow ref, resolve sub-expressions
            Expr::Dot {
                expr: Box::new(pre_resolve_expr(base, spec_name, w)),
                field: field.clone(),
            }
        }
        Expr::UnOp { op, expr: inner } => Expr::UnOp {
            op: *op,
            expr: Box::new(pre_resolve_expr(inner, spec_name, w)),
        },
        Expr::BinOp { op, left, right } => Expr::BinOp {
            op: *op,
            left: Box::new(pre_resolve_expr(left, spec_name, w)),
            right: Box::new(pre_resolve_expr(right, spec_name, w)),
        },
        _ => expr.clone(),
    }
}

fn branches_have_flow(stmts: &[Stmt]) -> bool {
    stmts
        .iter()
        .any(|s| matches!(s, Stmt::Call(_) | Stmt::FlowAssign { .. }))
}

fn branches_have_advance(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| matches!(s, Stmt::Advance(_)))
}

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
/// Negate an SMT expression. Simple variables use `(not (= x true))`
/// to match Go output; compound expressions use `(not expr)`.
fn negate_smt_expr(e: &str) -> String {
    if e.starts_with('(') {
        format!("(not {})", e)
    } else {
        format!("(not (= {} true))", e)
    }
}

/// Build `(and ...)` that avoids redundant wrapping for single elements.
fn smt_and(exprs: &[String]) -> String {
    if exprs.len() == 1 {
        exprs[0].clone()
    } else {
        format!("(and {})", exprs.join(" "))
    }
}

/// Build `(or ...)` that avoids redundant wrapping for single elements.
fn smt_or(exprs: &[String]) -> String {
    if exprs.len() == 1 {
        exprs[0].clone()
    } else {
        format!("(or {})", exprs.join(" "))
    }
}

/// Flatten a Dot chain to its constituent parts.
/// `Dot(Dot(Var("a"), "b"), "c")` → `["a", "b", "c"]`
fn flatten_dot_chain(expr: &Expr) -> Vec<String> {
    match expr {
        Expr::Var(name) => vec![name.clone()],
        Expr::Dot { expr: base, field } => {
            let mut parts = flatten_dot_chain(base);
            parts.push(field.clone());
            parts
        }
        _ => vec![],
    }
}

/// Determine SMT sort for a constant definition.
/// - String constants and expression constants (propositions) → Bool
/// - Bare constants (Unknown) and numeric constants → Real
fn const_sort(val: &Val, has_expr: bool) -> &'static str {
    if has_expr {
        return "Bool";
    }
    match val {
        Val::Str(_) => "Bool",
        Val::Bool(_) => "Bool",
        Val::Unknown | Val::Nat(_) | Val::Float(_) => "Real",
        _ => "Real",
    }
}

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
            imported_constants: vec![],
            import_alias_map: std::collections::HashMap::new(),
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
            imported_constants: vec![],
            import_alias_map: std::collections::HashMap::new(),
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
    fn e2e_strings() {
        let src = r#"spec test;
str1 = "is a fish";
str2 = "tastes delicious with ginger";
str3 = "native to North America";
str4 = !str1 && str2;

assume (str1 && str3) || str4;
assert str3;"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // All string vars declared as Bool
        assert!(lines.contains(&"(declare-fun test_str1_0 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun test_str2_0 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun test_str3_0 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun test_str4_0 () Bool)".into()));

        // Negation intermediate
        assert!(lines.contains(&"(declare-fun test_str1_neg_0 () Bool)".into()));
        assert!(lines.contains(&"(assert (= test_str1_neg_0 (not test_str1_0)))".into()));

        // str4 = !str1 && str2
        assert!(
            lines.contains(&"(assert (= test_str4_0 (and test_str2_0 test_str1_neg_0)))".into())
        );

        // Negated assertion
        assert!(lines.contains(&"(assert (not (= test_str3_0 true)))".into()));

        // Assumption
        assert!(lines.contains(&"(assert (or (and test_str1_0 test_str3_0) test_str4_0))".into()));
    }

    #[test]
    fn e2e_strings2() {
        let src = r#"spec test;
str1 = "is a fish";
str2 = "tastes delicious with ginger";
str3 = "native to North America";
str4 = "walks on four legs";
str5 = "has a tail";
str6 = "is blue";
str7 = (str1 && str2) || (str3 && str4);
str8 = str6 || str5 && str1;"#;

        let spec = fault_syntax::parser::parse_spec(src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // AND intermediates
        assert!(lines.contains(&"(declare-fun test_str3_test_str4_0 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun test_str1_test_str2_0 () Bool)".into()));
        assert!(lines.contains(&"(declare-fun test_str5_test_str1_0 () Bool)".into()));

        // AND constraints
        assert!(
            lines.contains(
                &"(assert (= test_str3_test_str4_0 (and test_str3_0 test_str4_0)))".into()
            )
        );
        assert!(
            lines.contains(
                &"(assert (= test_str1_test_str2_0 (and test_str1_0 test_str2_0)))".into()
            )
        );
        assert!(
            lines.contains(
                &"(assert (= test_str5_test_str1_0 (and test_str5_0 test_str1_0)))".into()
            )
        );

        // str7 = OR of AND intermediates
        assert!(lines.contains(
            &"(assert (= test_str7_0 (or test_str3_test_str4_0 test_str1_test_str2_0)))".into()
        ));

        // str8 = OR
        assert!(
            lines.contains(
                &"(assert (= test_str8_0 (or test_str5_test_str1_0 test_str6_0)))".into()
            )
        );
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

    #[test]
    fn e2e_indexes() {
        // bash.a[0] should always resolve to the initial value (version 0)
        let src = r#"spec indexes;
def foo = stock{ a: 10 };
def bar = flow{
    bash: new foo,
    fizz: func{ bash.a <- bash.a[0] - 2; },
};
for 2 init{ gee = new bar; } run { gee.fizz; };"#;
        let spec = fault_syntax::parser::parse_spec(&src).unwrap();
        let name = spec.name.clone();
        let resolved = fault_resolve::resolve_spec(spec);
        let smt = encode_program(&resolved, &name);
        let lines = normalize_smt(&smt);

        // Round 1: bash.a[0] = initial value (indexes_gee_bash_a_0)
        assert!(lines.contains(
            &"(assert (= indexes_gee_bash_a_1 (+ indexes_gee_bash_a_0 (- indexes_gee_bash_a_0 2.0))))".into()
        ));
        // Round 2: bash.a[0] still = initial value (indexes_gee_bash_a_0), not _1
        assert!(lines.contains(
            &"(assert (= indexes_gee_bash_a_2 (+ indexes_gee_bash_a_1 (- indexes_gee_bash_a_0 2.0))))".into()
        ));
    }
}
