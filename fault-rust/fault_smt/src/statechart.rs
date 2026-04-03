//! SMT-LIB2 encoding for statechart components.
//!
//! Mirrors the Go compiler's state machine encoding:
//! - Each component state → Bool variable with SSA versioning
//! - Start states → true, all others → false
//! - Advance(this.X) → set X to true (transition)
//! - Stay() → keep current state true
//! - AND transitions → conjunction of target states = true
//! - OR transitions → branch selectors with exclusivity
//! - Choose → like OR but with explicit negation of non-chosen states
//! - Each state function wrapped in ite(state==true, exec, skip) guard

use fault_syntax::{CompDef, Stmt, Expr, BinOp};
use std::collections::BTreeMap;

/// Extract the advance target from a name like `__advance_this.X` or `__advance_X`.
fn parse_advance_target(name: &str) -> &str {
    let without_prefix = name.strip_prefix("__advance_").unwrap_or(name);
    without_prefix.strip_prefix("this.").unwrap_or(without_prefix)
}

/// Tracks SSA versions and emitted declarations for state variables.
pub struct StateChartEncoder {
    spec_name: String,
    /// comp_state → current SSA version
    versions: BTreeMap<String, u32>,
    /// Accumulated declarations
    decls: Vec<String>,
    /// Accumulated assertions
    asserts: Vec<String>,
    /// Block counter for unique block guard names
    block_counter: u32,
}

impl StateChartEncoder {
    pub fn new(spec_name: &str) -> Self {
        Self {
            spec_name: spec_name.to_string(),
            versions: BTreeMap::new(),
            decls: Vec::new(),
            asserts: Vec::new(),
            block_counter: 0,
        }
    }

    /// Full qualified name: specname_comp_state
    fn qname(&self, comp: &str, state: &str) -> String {
        // Cross-component reference: "otherComp.stateName" → spec_otherComp_stateName
        if let Some(dot) = state.find('.') {
            let target_comp = &state[..dot];
            let target_state = &state[dot + 1..];
            format!("{}_{}_{}", self.spec_name, target_comp, target_state)
        } else {
            format!("{}_{}_{}", self.spec_name, comp, state)
        }
    }

    /// Declare a new SSA version of a state variable and return its name.
    fn next_version(&mut self, comp: &str, state: &str) -> String {
        let base = self.qname(comp, state);
        let ver = self.versions.entry(base.clone()).or_insert(0);
        *ver += 1;
        let name = format!("{}_{}", base, *ver);
        self.decls.push(format!("(declare-fun {} () Bool)", name));
        name
    }

    /// Declare initial version (version 0) for a state variable.
    fn declare_initial(&mut self, comp: &str, state: &str) {
        let base = self.qname(comp, state);
        self.versions.insert(base.clone(), 0);
        self.decls.push(format!("(declare-fun {}_0 () Bool)", base));
    }

    fn next_block_id(&mut self) -> u32 {
        let id = self.block_counter;
        self.block_counter += 1;
        id
    }

    /// Encode all components and return (declarations, assertions).
    pub fn encode(
        &mut self,
        components: &[CompDef],
        start_states: &[(String, String)],
    ) -> (Vec<String>, Vec<String>) {
        // Phase 1: Declare initial state variables
        for comp in components {
            for (state_name, _) in &comp.states {
                self.declare_initial(&comp.name, state_name);
            }
        }

        // Set initial values: all false
        for comp in components {
            for (state_name, _) in &comp.states {
                let v0 = format!("{}_0", self.qname(&comp.name, state_name));
                self.asserts.push(format!("(assert (= {} false))", v0));
            }
        }

        // Set start states: version 1 = true
        for (comp_name, state_name) in start_states {
            let v1 = self.next_version(comp_name, state_name);
            self.asserts.push(format!("(assert (= {} true))", v1));
        }

        // Phase 2: Encode each component's state functions
        for comp in components {
            self.encode_component(comp);
        }

        (self.decls.clone(), self.asserts.clone())
    }

    /// Encode components using pre-initialized version state.
    /// Used by mixed system encoder after SmtWriter has handled init/start states.
    pub fn encode_components_with_versions(
        &mut self,
        components: &[CompDef],
        initial_versions: &BTreeMap<String, u32>,
    ) -> (Vec<String>, Vec<String>) {
        self.versions = initial_versions.clone();
        for comp in components {
            self.encode_component(comp);
        }
        (self.decls.clone(), self.asserts.clone())
    }

    fn encode_component(&mut self, comp: &CompDef) {
        let state_names: Vec<String> = comp.states.iter().map(|(n, _)| n.clone()).collect();

        for (state_name, body) in &comp.states {
            self.encode_state_function(&comp.name, state_name, body, &state_names);
        }
    }

    /// Encode a single state function with ite guard.
    ///
    /// Records pre-encoding versions for proper guard and false-branch handling.
    fn encode_state_function(
        &mut self,
        comp_name: &str,
        state_name: &str,
        body: &[Stmt],
        all_states: &[String],
    ) {
        // Snapshot pre-encoding versions for all states
        let pre_versions: BTreeMap<String, u32> = all_states
            .iter()
            .map(|s| {
                let base = self.qname(comp_name, s);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (s.clone(), ver)
            })
            .collect();

        let transition = analyze_body(body);

        match transition {
            Transition::Stay => {
                self.encode_stay_body(comp_name, state_name);
            }
            Transition::AdvanceAnd(targets) => {
                self.encode_advance_and_body(comp_name, state_name, &targets);
            }
            Transition::AdvanceOr(targets) => {
                self.encode_advance_or_body(comp_name, state_name, &targets, &pre_versions);
            }
            Transition::ChooseOr(branches) => {
                self.encode_choose_body(comp_name, state_name, &branches, all_states);
            }
            Transition::CompoundChoose(branches) => {
                self.encode_compound_choose_body(comp_name, state_name, &branches, all_states);
            }
            Transition::Conditional(cond, then_trans, else_trans) => {
                self.encode_conditional(
                    comp_name,
                    state_name,
                    &cond,
                    &then_trans,
                    else_trans.as_deref(),
                    all_states,
                );
                return; // TODO: conditional handles its own guard
            }
            Transition::Empty => return,
        }

        // Emit ite guard using pre-encoding versions
        self.emit_ite_guard(comp_name, state_name, all_states, &pre_versions);
    }

    /// Emit the ite guard wrapping a state function's body.
    ///
    /// If the state is active (guard=true), carry forward post-body versions;
    /// otherwise, reset to pre-body versions.
    fn emit_ite_guard(
        &mut self,
        comp: &str,
        state: &str,
        all_states: &[String],
        pre_versions: &BTreeMap<String, u32>,
    ) {
        let guard_base = self.qname(comp, state);
        let guard_ver = pre_versions[state];
        let guard_var = format!("{}_{}", guard_base, guard_ver);

        // Collect all states that changed during encoding
        let mut changed: Vec<String> = Vec::new();
        for s in all_states {
            let base = self.qname(comp, s);
            let post_ver = *self.versions.get(&base).unwrap_or(&0);
            let pre_ver = pre_versions.get(s).copied().unwrap_or(0);
            if post_ver != pre_ver {
                changed.push(s.clone());
            }
        }

        if changed.is_empty() {
            return;
        }

        let block_id = self.next_block_id();
        let bt = format!("block{}true_0", block_id);
        let bf = format!("block{}false_0", block_id);
        self.decls.push(format!("(declare-fun {} () Bool)", bt));
        self.decls.push(format!("(declare-fun {} () Bool)", bf));

        let mut true_eqs = vec![
            format!("(= {} true)", bt),
            format!("(= {} false)", bf),
        ];
        let mut false_eqs = vec![
            format!("(= {} false)", bt),
            format!("(= {} true)", bf),
        ];

        let mut carry_true = Vec::new();
        let mut carry_false = Vec::new();
        for s in &changed {
            let base = self.qname(comp, s);
            let post_ver = self.versions[&base];
            let pre_ver = pre_versions[s];
            let curr_var = format!("{}_{}", base, post_ver);
            let pre_var = format!("{}_{}", base, pre_ver);
            let result = self.next_version(comp, s);
            carry_true.push(format!("(= {} {})", result, curr_var));
            carry_false.push(format!("(= {} {})", result, pre_var));
        }
        if carry_true.len() == 1 {
            true_eqs.push(carry_true[0].clone());
            false_eqs.push(carry_false[0].clone());
        } else {
            true_eqs.push(format!("(and {})", carry_true.join(" ")));
            false_eqs.push(format!("(and {})", carry_false.join(" ")));
        }

        self.asserts.push(format!(
            "(assert (ite (= {} true) (and {}) (and {})))",
            guard_var,
            true_eqs.join(" "),
            false_eqs.join(" ")
        ));

        self.asserts.push(format!(
            "(assert (or (and {} (not {})) (and (not {}) {})))",
            bt, bf, bt, bf
        ));
    }

    /// Encode stay() body: emit the transition value (stay = true).
    fn encode_stay_body(&mut self, comp: &str, state: &str) {
        let stay_val = self.next_version(comp, state);
        self.asserts
            .push(format!("(assert (= {} true))", stay_val));
    }

    /// Encode advance(X) && advance(Y) body: emit transition assertions.
    fn encode_advance_and_body(&mut self, comp: &str, _state: &str, targets: &[String]) {
        let mut target_eqs = Vec::new();
        for target in targets {
            let v = self.next_version(comp, target);
            target_eqs.push(format!("(= {} true)", v));
        }
        if target_eqs.len() == 1 {
            self.asserts.push(format!("(assert {})", target_eqs[0]));
        } else {
            self.asserts
                .push(format!("(assert (and {}))", target_eqs.join(" ")));
        }
    }

    /// Encode advance(X) || advance(Y) body: selectors, implications, carry-forward.
    fn encode_advance_or_body(
        &mut self,
        comp: &str,
        state: &str,
        targets: &[String],
        pre_versions: &BTreeMap<String, u32>,
    ) {
        let num_branches = targets.len();

        let sel_base = format!("{}__state-%8", self.qname(comp, state));
        let mut selectors = Vec::new();
        for i in 0..num_branches {
            let sel = format!("{}_{}", sel_base, i);
            self.decls.push(format!("(declare-fun {} () Bool)", sel));
            selectors.push(sel);
        }

        // Each branch only sets its own target
        for (i, target) in targets.iter().enumerate() {
            let v = self.next_version(comp, target);
            self.asserts.push(format!(
                "(assert (=> {} (= {} true)))",
                selectors[i], v
            ));
        }

        // Shared carry-forward
        let mut carry_vars = Vec::new();
        for target in targets {
            let v = self.next_version(comp, target);
            carry_vars.push(v);
        }

        for (i, _target) in targets.iter().enumerate() {
            let mut eqs = Vec::new();
            for (j, other_target) in targets.iter().enumerate() {
                let tbase = self.qname(comp, other_target);
                if j == i {
                    // Active target: carry forward the transition value
                    let trans_ver = self.versions[&tbase] - 1;
                    eqs.push(format!("(= {} {}_{})", carry_vars[j], tbase, trans_ver));
                } else {
                    // Inactive target: use pre-body version (not version 0)
                    let pre_ver = pre_versions.get(other_target).copied().unwrap_or(0);
                    eqs.push(format!("(= {} {}_{})", carry_vars[j], tbase, pre_ver));
                }
            }
            let eq_str = if eqs.len() == 1 {
                eqs[0].clone()
            } else {
                format!("(and {})", eqs.join("\n"))
            };
            self.asserts
                .push(format!("(assert (= {} {}))", selectors[i], eq_str));
        }

        self.emit_exclusivity(&selectors);
    }

    /// Encode choose body: selectors, implications, carry-forward for all affected vars.
    fn encode_choose_body(
        &mut self,
        comp: &str,
        state: &str,
        branches: &[ChooseBranch],
        _all_states: &[String],
    ) {
        // Collect all affected state names across all branches.
        let mut affected: Vec<String> = Vec::new();
        for branch in branches {
            match branch {
                ChooseBranch::Advance(t) => {
                    if !affected.contains(t) {
                        affected.push(t.clone());
                    }
                }
                ChooseBranch::AdvanceAnd(ts) => {
                    for t in ts {
                        if !affected.contains(t) {
                            affected.push(t.clone());
                        }
                    }
                }
                ChooseBranch::Stay => {
                    if !affected.contains(&state.to_string()) {
                        affected.push(state.to_string());
                    }
                }
            }
        }

        if affected.is_empty() {
            return;
        }

        let num_branches = branches.len();

        // Create selector variables
        let sel_base = format!("{}__state-%8", self.qname(comp, state));
        let mut selectors = Vec::new();
        for i in 0..num_branches {
            let sel = format!("{}_{}", sel_base, i);
            self.decls.push(format!("(declare-fun {} () Bool)", sel));
            selectors.push(sel);
        }

        // For each branch, determine active targets
        let branch_active: Vec<Vec<String>> = branches
            .iter()
            .map(|b| match b {
                ChooseBranch::Advance(t) => vec![t.clone()],
                ChooseBranch::AdvanceAnd(ts) => ts.clone(),
                ChooseBranch::Stay => vec![state.to_string()],
            })
            .collect();

        // branch_versions[i][j] = version name for affected[j] in branch i
        let mut branch_versions: Vec<Vec<String>> = Vec::new();

        // For each branch, create versions for ALL affected vars
        for (i, active) in branch_active.iter().enumerate() {
            let mut this_branch = Vec::new();
            let mut parts = Vec::new();
            for aff in &affected {
                let v = self.next_version(comp, aff);
                this_branch.push(v.clone());
                if active.contains(aff) {
                    parts.push(format!("(= {} true)", v));
                } else {
                    parts.push(format!("(not (= {} true))", v));
                }
            }
            self.asserts.push(format!(
                "(assert (=> {} (and {})))",
                selectors[i],
                parts.join(" ")
            ));
            branch_versions.push(this_branch);
        }

        // Shared carry-forward variables for all affected vars
        let mut carry_vars = Vec::new();
        for aff in &affected {
            let v = self.next_version(comp, aff);
            carry_vars.push(v);
        }

        // Branch carry-forward: selector <=> carry = branch's versions
        for (i, _branch) in branches.iter().enumerate() {
            let mut eqs = Vec::new();
            for (j, _aff) in affected.iter().enumerate() {
                eqs.push(format!(
                    "(= {} {})",
                    carry_vars[j], branch_versions[i][j]
                ));
            }
            let eq_str = if eqs.len() == 1 {
                eqs[0].clone()
            } else {
                format!("(and {})", eqs.join("\n"))
            };
            self.asserts
                .push(format!("(assert (= {} {}))", selectors[i], eq_str));
        }

        // Exclusivity
        self.emit_exclusivity(&selectors);
    }

    /// Encode compound Or/And choose body: only bump ACTIVE targets per branch.
    /// Used for CompoundTransition with mixed Or/And (not explicit choose keyword).
    fn encode_compound_choose_body(
        &mut self,
        comp: &str,
        state: &str,
        branches: &[ChooseBranch],
        _all_states: &[String],
    ) {
        // Collect all affected target states across all branches
        let mut affected: Vec<String> = Vec::new();
        for branch in branches {
            match branch {
                ChooseBranch::Advance(t) => {
                    if !affected.contains(t) {
                        affected.push(t.clone());
                    }
                }
                ChooseBranch::AdvanceAnd(ts) => {
                    for t in ts {
                        if !affected.contains(t) {
                            affected.push(t.clone());
                        }
                    }
                }
                ChooseBranch::Stay => {
                    if !affected.contains(&state.to_string()) {
                        affected.push(state.to_string());
                    }
                }
            }
        }

        if affected.is_empty() {
            return;
        }

        let num_branches = branches.len();

        // Create selector variables
        let sel_base = format!("{}__state-%8", self.qname(comp, state));
        let mut selectors = Vec::new();
        for i in 0..num_branches {
            let sel = format!("{}_{}", sel_base, i);
            self.decls.push(format!("(declare-fun {} () Bool)", sel));
            selectors.push(sel);
        }

        // Pre-body versions
        let pre_versions: BTreeMap<String, u32> = affected
            .iter()
            .map(|a| {
                let base = self.qname(comp, a);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (a.clone(), ver)
            })
            .collect();

        // For each branch, determine active targets
        let branch_active: Vec<Vec<String>> = branches
            .iter()
            .map(|b| match b {
                ChooseBranch::Advance(t) => vec![t.clone()],
                ChooseBranch::AdvanceAnd(ts) => ts.clone(),
                ChooseBranch::Stay => vec![state.to_string()],
            })
            .collect();

        // Only bump active targets per branch
        let mut branch_target_versions: Vec<BTreeMap<String, String>> = Vec::new();
        for (i, active) in branch_active.iter().enumerate() {
            let mut target_vers = BTreeMap::new();
            let mut parts = Vec::new();
            for target in active {
                let v = self.next_version(comp, target);
                target_vers.insert(target.clone(), v.clone());
                parts.push(format!("(= {} true)", v));
            }
            if parts.len() == 1 {
                self.asserts.push(format!(
                    "(assert (=> {} {}))",
                    selectors[i], parts[0]
                ));
            } else {
                self.asserts.push(format!(
                    "(assert (=> {} (and {})))",
                    selectors[i],
                    parts.join("\n")
                ));
            }
            branch_target_versions.push(target_vers);
        }

        // Shared carry-forward for ALL affected vars
        let mut carry_vars: BTreeMap<String, String> = BTreeMap::new();
        for aff in &affected {
            let v = self.next_version(comp, aff);
            carry_vars.insert(aff.clone(), v);
        }

        // selector <=> carry = branch's active versions or pre-body versions
        for (i, active) in branch_active.iter().enumerate() {
            let mut eqs = Vec::new();
            for aff in &affected {
                let carry = &carry_vars[aff];
                if active.contains(aff) {
                    let trans_ver = &branch_target_versions[i][aff];
                    eqs.push(format!("(= {} {})", carry, trans_ver));
                } else {
                    let base = self.qname(comp, aff);
                    let pre_ver = pre_versions[aff];
                    eqs.push(format!("(= {} {}_{})", carry, base, pre_ver));
                }
            }
            let eq_str = if eqs.len() == 1 {
                eqs[0].clone()
            } else {
                format!("(and {})", eqs.join("\n"))
            };
            self.asserts
                .push(format!("(assert (= {} {}))", selectors[i], eq_str));
        }

        self.emit_exclusivity(&selectors);
    }

    /// Encode if-then-else conditional transition.
    ///
    /// Go encoding pattern:
    /// 1. Encode else-branch transitions (bumps vars)
    /// 2. Emit ite guard with just state-active condition
    /// 3. Encode then-branch transitions (bumps vars further)
    /// 4. Emit ite guard with (state-active AND user-condition)
    ///
    /// When condition is true: then-body results are selected (overwriting else)
    /// When condition is false: else-body results pass through
    /// When state not active: both ite guards take false path → pre versions
    fn encode_conditional(
        &mut self,
        comp: &str,
        state: &str,
        condition: &Expr,
        then_trans: &Transition,
        else_trans: Option<&Transition>,
        all_states: &[String],
    ) {
        // Pre-versions for the entire conditional
        let pre_versions: BTreeMap<String, u32> = all_states
            .iter()
            .map(|s| {
                let base = self.qname(comp, s);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (s.clone(), ver)
            })
            .collect();

        let guard_base = self.qname(comp, state);
        let _guard_ver = pre_versions[state];

        // Step 1: Encode else-branch body (if present)
        if let Some(else_t) = else_trans {
            self.encode_transition_body(comp, state, else_t, all_states);
        }

        // Step 2: Emit ite guard for else-branch with just state-active
        let post_else_versions: BTreeMap<String, u32> = all_states
            .iter()
            .map(|s| {
                let base = self.qname(comp, s);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (s.clone(), ver)
            })
            .collect();

        if post_else_versions != pre_versions {
            self.emit_ite_guard(comp, state, all_states, &pre_versions);
        }

        // Snapshot versions after else ite guard
        let mid_versions: BTreeMap<String, u32> = all_states
            .iter()
            .map(|s| {
                let base = self.qname(comp, s);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (s.clone(), ver)
            })
            .collect();

        // Step 3: Encode then-branch body
        self.encode_transition_body(comp, state, then_trans, all_states);

        // Step 4: Emit ite guard with (state-active AND condition)
        let post_then_versions: BTreeMap<String, u32> = all_states
            .iter()
            .map(|s| {
                let base = self.qname(comp, s);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (s.clone(), ver)
            })
            .collect();

        if post_then_versions == mid_versions {
            return; // then body produced nothing
        }

        let guard_var = format!("{}_{}", guard_base, mid_versions[state]);
        let cond_smt = cond_expr_to_smt(condition);
        let combined_guard = format!("(and (= {} true) {})", guard_var, cond_smt);

        // Build ite with combined guard, using mid_versions as false-branch
        let mut changed: Vec<String> = Vec::new();
        for s in all_states {
            let base = self.qname(comp, s);
            let post_ver = *self.versions.get(&base).unwrap_or(&0);
            let mid_ver = mid_versions.get(s).copied().unwrap_or(0);
            if post_ver != mid_ver {
                changed.push(s.clone());
            }
        }

        if changed.is_empty() {
            return;
        }

        let block_id = self.next_block_id();
        let bt = format!("block{}true_0", block_id);
        let bf = format!("block{}false_0", block_id);
        self.decls.push(format!("(declare-fun {} () Bool)", bt));
        self.decls.push(format!("(declare-fun {} () Bool)", bf));

        let mut true_eqs = vec![
            format!("(= {} true)", bt),
            format!("(= {} false)", bf),
        ];
        let mut false_eqs = vec![
            format!("(= {} false)", bt),
            format!("(= {} true)", bf),
        ];

        let mut carry_true = Vec::new();
        let mut carry_false = Vec::new();
        for s in &changed {
            let base = self.qname(comp, s);
            let post_ver = self.versions[&base];
            let mid_ver = mid_versions[s];
            let curr_var = format!("{}_{}", base, post_ver);
            let mid_var = format!("{}_{}", base, mid_ver);
            let result = self.next_version(comp, s);
            carry_true.push(format!("(= {} {})", result, curr_var));
            carry_false.push(format!("(= {} {})", result, mid_var));
        }
        if carry_true.len() == 1 {
            true_eqs.push(carry_true[0].clone());
            false_eqs.push(carry_false[0].clone());
        } else {
            true_eqs.push(format!("(and {})", carry_true.join(" ")));
            false_eqs.push(format!("(and {})", carry_false.join(" ")));
        }

        self.asserts.push(format!(
            "(assert (ite {} (and {}) (and {})))",
            combined_guard,
            true_eqs.join(" "),
            false_eqs.join(" ")
        ));

        self.asserts.push(format!(
            "(assert (or (and {} (not {})) (and (not {}) {})))",
            bt, bf, bt, bf
        ));
    }

    /// Encode a transition body (dispatches to the appropriate method).
    fn encode_transition_body(
        &mut self,
        comp: &str,
        state: &str,
        trans: &Transition,
        all_states: &[String],
    ) {
        let pre_versions: BTreeMap<String, u32> = all_states
            .iter()
            .map(|s| {
                let base = self.qname(comp, s);
                let ver = *self.versions.get(&base).unwrap_or(&0);
                (s.clone(), ver)
            })
            .collect();
        match trans {
            Transition::Stay => self.encode_stay_body(comp, state),
            Transition::AdvanceAnd(targets) => self.encode_advance_and_body(comp, state, targets),
            Transition::AdvanceOr(targets) => {
                self.encode_advance_or_body(comp, state, targets, &pre_versions);
            }
            Transition::ChooseOr(branches) => {
                self.encode_choose_body(comp, state, branches, all_states);
            }
            Transition::CompoundChoose(branches) => {
                self.encode_compound_choose_body(comp, state, branches, all_states);
            }
            Transition::Conditional(cond, then_t, else_t) => {
                self.encode_conditional(comp, state, cond, then_t, else_t.as_deref(), all_states);
            }
            Transition::Empty => {}
        }
    }

    /// Emit exclusivity constraint: exactly one of the selectors is true.
    fn emit_exclusivity(&mut self, selectors: &[String]) {
        if selectors.len() == 2 {
            self.asserts.push(format!(
                "(assert (or (and {} (not {})) (and (not {}) {})))",
                selectors[0], selectors[1], selectors[0], selectors[1]
            ));
        } else {
            let mut clauses = Vec::new();
            for (i, sel) in selectors.iter().enumerate() {
                let mut parts = Vec::new();
                for (j, other) in selectors.iter().enumerate() {
                    if i == j {
                        parts.push(sel.clone());
                    } else {
                        parts.push(format!("(not {})", other));
                    }
                }
                clauses.push(format!("(and {})", parts.join(" ")));
            }
            self.asserts
                .push(format!("(assert (or {}))", clauses.join(" ")));
        }
    }
}

// ── Analysis ──────────────────────────────────────────────────────────

/// Analyzed transition from a state function body.
#[derive(Debug, Clone)]
enum Transition {
    Empty,
    Stay,
    /// advance(X) && advance(Y) — all targets simultaneously
    AdvanceAnd(Vec<String>),
    /// advance(X) || advance(Y) — exclusive branches
    AdvanceOr(Vec<String>),
    /// choose — solver-chosen branches (bump ALL affected vars per branch)
    ChooseOr(Vec<ChooseBranch>),
    /// compound Or/And transition — bump only ACTIVE targets per branch
    CompoundChoose(Vec<ChooseBranch>),
    /// if cond then transition else transition
    Conditional(Expr, Box<Transition>, Option<Box<Transition>>),
}

#[derive(Debug, Clone)]
enum ChooseBranch {
    Advance(String),
    AdvanceAnd(Vec<String>),
    Stay,
}

/// Analyze a state function body to determine transition type.
fn analyze_body(body: &[Stmt]) -> Transition {
    if body.is_empty() {
        return Transition::Empty;
    }

    if body.len() == 1 {
        return analyze_stmt(&body[0]);
    }

    // Multiple statements: check for if-then-else
    if let Some(Stmt::IfThenElse {
        cond,
        then_branch,
        else_branch,
    }) = body.first()
    {
        let then_t = analyze_body(then_branch);
        let else_t = if else_branch.is_empty() {
            None
        } else {
            Some(Box::new(analyze_body(else_branch)))
        };
        return Transition::Conditional(cond.clone(), Box::new(then_t), else_t);
    }

    Transition::Empty
}

fn analyze_stmt(stmt: &Stmt) -> Transition {
    match stmt {
        Stmt::Stay => Transition::Stay,
        Stmt::Advance(target) => {
            let state = target.strip_prefix("this.").unwrap_or(target).to_string();
            Transition::AdvanceAnd(vec![state])
        }
        Stmt::CompoundTransition(expr) => analyze_expr(expr),
        Stmt::ChooseTransition(expr) => {
            let branches = extract_choose_branches(expr);
            Transition::ChooseOr(branches)
        }
        Stmt::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_t = analyze_body(then_branch);
            let else_t = if else_branch.is_empty() {
                None
            } else {
                Some(Box::new(analyze_body(else_branch)))
            };
            Transition::Conditional(cond.clone(), Box::new(then_t), else_t)
        }
        _ => Transition::Empty,
    }
}

fn analyze_expr(expr: &Expr) -> Transition {
    match expr {
        Expr::BinOp {
            op: BinOp::And,
            left,
            right,
        } => {
            let mut targets = Vec::new();
            collect_and_targets(left, &mut targets);
            collect_and_targets(right, &mut targets);
            if targets.is_empty() {
                Transition::Empty
            } else {
                Transition::AdvanceAnd(targets)
            }
        }
        Expr::BinOp {
            op: BinOp::Or,
            left,
            right,
        } => {
            // Check if any branch has nested AND — if so, use CompoundChoose
            if or_has_and_branch(expr) {
                let branches = extract_choose_branches(expr);
                if branches.is_empty() {
                    Transition::Empty
                } else {
                    Transition::CompoundChoose(branches)
                }
            } else {
                let mut targets = Vec::new();
                collect_or_targets(left, &mut targets);
                collect_or_targets(right, &mut targets);
                if targets.is_empty() {
                    Transition::Empty
                } else {
                    Transition::AdvanceOr(targets)
                }
            }
        }
        Expr::Var(name) if name.starts_with("__advance_") => {
            let target = parse_advance_target(name).to_string();
            Transition::AdvanceAnd(vec![target])
        }
        Expr::Var(name) if name == "__stay" => Transition::Stay,
        _ => Transition::Empty,
    }
}

/// Check if an Or expression has any branch that's an And (mixed pattern).
fn or_has_and_branch(expr: &Expr) -> bool {
    match expr {
        Expr::BinOp { op: BinOp::Or, left, right } => {
            or_has_and_branch(left) || or_has_and_branch(right)
        }
        Expr::BinOp { op: BinOp::And, .. } => true,
        _ => false,
    }
}

fn collect_and_targets(expr: &Expr, targets: &mut Vec<String>) {
    match expr {
        Expr::BinOp {
            op: BinOp::And,
            left,
            right,
        } => {
            collect_and_targets(left, targets);
            collect_and_targets(right, targets);
        }
        Expr::Var(name) if name.starts_with("__advance_") => {
            let target = parse_advance_target(name).to_string();
            targets.push(target);
        }
        _ => {}
    }
}

fn collect_or_targets(expr: &Expr, targets: &mut Vec<String>) {
    match expr {
        Expr::BinOp {
            op: BinOp::Or,
            left,
            right,
        } => {
            collect_or_targets(left, targets);
            collect_or_targets(right, targets);
        }
        Expr::Var(name) if name.starts_with("__advance_") => {
            let target = parse_advance_target(name).to_string();
            targets.push(target);
        }
        _ => {}
    }
}

fn extract_choose_branches(expr: &Expr) -> Vec<ChooseBranch> {
    let mut branches = Vec::new();
    collect_choose_branches(expr, &mut branches);
    branches
}

fn collect_choose_branches(expr: &Expr, branches: &mut Vec<ChooseBranch>) {
    match expr {
        Expr::BinOp {
            op: BinOp::Or,
            left,
            right,
        } => {
            collect_choose_branches(left, branches);
            collect_choose_branches(right, branches);
        }
        Expr::BinOp {
            op: BinOp::And,
            left,
            right,
        } => {
            let mut targets = Vec::new();
            collect_and_targets(left, &mut targets);
            collect_and_targets(right, &mut targets);
            branches.push(ChooseBranch::AdvanceAnd(targets));
        }
        Expr::Var(name) if name.starts_with("__advance_") => {
            let target = parse_advance_target(name).to_string();
            branches.push(ChooseBranch::Advance(target));
        }
        Expr::Var(name) if name == "__stay" => {
            branches.push(ChooseBranch::Stay);
        }
        _ => {}
    }
}

/// Render a condition expression to SMT-LIB2.
/// Used for pre-resolved conditions where Dot chains have been replaced
/// with qualified Var names (e.g., `Var("mixedcalls_fl_active_0")`).
fn cond_expr_to_smt(expr: &Expr) -> String {
    match expr {
        Expr::Var(name) => {
            // Pre-resolved vars are already qualified with spec_name and version
            format!("(= {} true)", name)
        }
        Expr::UnOp { op: fault_syntax::UnOp::Not, expr: inner } => {
            let inner_smt = cond_expr_to_smt_bare(inner);
            format!("(not {})", inner_smt)
        }
        Expr::BinOp { op: BinOp::And, left, right } => {
            format!("(and {} {})", cond_expr_to_smt(left), cond_expr_to_smt(right))
        }
        Expr::BinOp { op: BinOp::Or, left, right } => {
            format!("(or {} {})", cond_expr_to_smt(left), cond_expr_to_smt(right))
        }
        // Comparison operators
        Expr::BinOp { op: BinOp::Eq, left, right } => {
            format!("(= {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Neq, left, right } => {
            format!("(not (= {} {}))", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Lt, left, right } => {
            format!("(< {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Le, left, right } => {
            format!("(<= {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Gt, left, right } => {
            format!("(> {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Ge, left, right } => {
            format!("(>= {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        // Arithmetic operators (for nested expressions in conditions)
        Expr::BinOp { op: BinOp::Add, left, right } => {
            format!("(+ {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Sub, left, right } => {
            format!("(- {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Mul, left, right } => {
            format!("(* {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::BinOp { op: BinOp::Div, left, right } => {
            format!("(/ {} {})", cond_expr_to_smt_bare(left), cond_expr_to_smt_bare(right))
        }
        Expr::Lit(val) => match val {
            fault_syntax::Val::Bool(b) => b.to_string(),
            fault_syntax::Val::Nat(n) => format!("{}.0", n),
            fault_syntax::Val::Float(f) => format!("{}", f),
            fault_syntax::Val::Str(s) => format!("\"{}\"", s),
            _ => format!("{:?}", val),
        },
        _ => format!("; ERROR: cond_expr_to_smt: unhandled {:?}", expr),
    }
}

/// Render a condition expression to SMT-LIB2 without Bool wrapping.
fn cond_expr_to_smt_bare(expr: &Expr) -> String {
    match expr {
        Expr::Var(name) => name.clone(),
        _ => cond_expr_to_smt(expr),
    }
}
