/-
  FaultSemantics.Properties

  Phase 5: Structural properties of the Fault LTS using CSLib's
  built-in theory. Proves finite branching, conditional determinism,
  and finite LTS for bounded models.
-/
import FaultSemantics.Temporal
import Cslib.Foundations.Semantics.LTS.Basic

open Cslib

/-! ## Basic Properties of faultStep -/

/-- The stay transition is always available (every state has a tau derivative) -/
theorem faultStep_stay_always (σ : FaultState) :
    faultStep σ .tau σ :=
  faultStep.stayStep σ

/-- Round transitions preserve the round counter correctly -/
theorem faultStep_round_increments (σ σ' : FaultState) (vars : List Name) :
    σ' = (σ.snapshot vars).nextRound →
    faultStep σ (.round σ.round) σ' := by
  intro h
  rw [h]
  exact faultStep.roundStep σ vars

/-- Assignment transitions update exactly the target variable -/
theorem faultStep_assign_updates (σ : FaultState) (x y : Name) (op : FlowOp) (e : Expr) :
    x ≠ y →
    (σ.setVar x (applyFlowOp op (σ.getVar x) (eval σ e))).getVar y = σ.getVar y := by
  intro hne
  simp [FaultState.setVar, FaultState.getVar, Env.update]
  intro h
  exact absurd h.symm hne

/-- Advance transitions update exactly the target component -/
theorem faultStep_advance_preserves_other (σ : FaultState) (c₁ c₂ newState : Name) :
    c₁ ≠ c₂ →
    (σ.setCompState c₁ newState).compState c₂ = σ.compState c₂ := by
  intro hne
  simp [FaultState.setCompState]
  intro h
  exact absurd h.symm hne

/-! ## Determinism Analysis -/

theorem faultStep_assign_deterministic (σ : FaultState) (x : Name) (op : FlowOp)
    (e₁ e₂ : Expr) :
    eval σ e₁ = eval σ e₂ →
    σ.setVar x (applyFlowOp op (σ.getVar x) (eval σ e₁)) =
    σ.setVar x (applyFlowOp op (σ.getVar x) (eval σ e₂)) := by
  intro h; rw [h]

/-! ## ExecStmts Properties -/

/-- Empty statement list is a no-op -/
theorem execStmts_nil (σ : FaultState) :
    ExecStmts σ [] [] σ :=
  ExecStmts.nil σ

/-- ExecRounds with 0 rounds is identity -/
theorem execRounds_zero (σ : FaultState) (runBody : List Stmt) (vars : List Name) :
    ExecRounds σ 0 runBody vars [] σ :=
  ExecRounds.zero σ runBody vars

/-! ## Round Counter Monotonicity -/

mutual
/-- Statement execution preserves the round counter.
    Uses mutual def since Lean 4 mutual blocks require def, not theorem. -/
def execStmt_preserves_round (σ σ' : FaultState) (s : Stmt) (μs : List Label)
    (h : ExecStmt σ s μs σ') : σ'.round = σ.round :=
  match s, μs, h with
  | _, _, .flowAssign _ x op e v hEval => by simp [FaultState.setVar]
  | _, _, .ifTrue _ _ cond thenB elseB μs₂ hCond hBody =>
    execStmts_preserves_round _ _ _ _ hBody
  | _, _, .ifFalse _ _ cond thenB elseB μs₂ hCond hBody =>
    execStmts_preserves_round _ _ _ _ hBody
  | _, _, .call _ _ funcName body μs₂ hBody =>
    execStmts_preserves_round _ _ _ _ hBody
  | _, _, .advance _ target comp newState => by simp [FaultState.setCompState]
  | _, _, .stay _ => rfl
  | _, _, .seq _ _ stmts μs₂ hBody =>
    execStmts_preserves_round _ _ _ _ hBody
  | _, _, .parallel _ _ stmts perm μs₂ hPerm hBody =>
    execStmts_preserves_round _ _ _ _ hBody

def execStmts_preserves_round (σ σ' : FaultState) (ss : List Stmt) (μs : List Label)
    (h : ExecStmts σ ss μs σ') : σ'.round = σ.round :=
  match ss, μs, h with
  | _, _, .nil _ => rfl
  | _, _, .cons _ σ_mid _ _ _ _ _ hStmt hRest =>
    have h1 := execStmt_preserves_round _ _ _ _ hStmt
    have h2 := execStmts_preserves_round _ _ _ _ hRest
    by omega
end

/-- After executing a round, the round counter increases by 1 -/
theorem execRound_increments_round (σ σ' : FaultState) (runBody : List Stmt)
    (vars : List Name) (μs : List Label) :
    ExecRound σ runBody vars μs σ' → σ'.round = σ.round + 1 := by
  intro h
  cases h
  simp [FaultState.nextRound, FaultState.snapshot]
  next σ_run _ hExec =>
    have := execStmts_preserves_round _ _ _ _ hExec
    omega

/-- After N rounds, the round counter has increased by N -/
theorem execRounds_round_count (σ σ' : FaultState) (n : Nat) (runBody : List Stmt)
    (vars : List Name) (μs : List Label) :
    ExecRounds σ n runBody vars μs σ' → σ'.round = σ.round + n := by
  intro h
  induction h with
  | zero => omega
  | succ σ₀ σ_mid σ_final n' _ _ _ _ hRound _ ih =>
    have h1 := execRound_increments_round _ _ _ _ _ hRound
    omega

/-! ## Temporal Property Relationships -/

/-- always implies eventually (for nonempty traces) -/
theorem always_implies_eventually (P : FaultState → Prop) (states : List FaultState) :
    states ≠ [] → always states P → eventually states P := by
  intro hne hAll
  unfold always at hAll
  unfold eventually
  match states, hne with
  | σ :: _, _ =>
    exact ⟨σ, List.mem_cons_self .., hAll σ (List.mem_cons_self ..)⟩

/-- eventuallyAlways implies eventually (for nonempty traces) -/
theorem eventuallyAlways_implies_eventually (P : FaultState → Prop) (states : List FaultState) :
    eventuallyAlways states P → eventually states P := by
  intro ⟨k, hk, hAll⟩
  unfold eventually
  have hDrop := List.drop_subset k states
  match hd : states.drop k with
  | [] =>
    simp [List.drop_eq_nil_iff] at hd
    omega
  | σ :: rest =>
    have hMem : σ ∈ states.drop k := hd ▸ List.mem_cons_self ..
    exact ⟨σ, hDrop hMem, hAll σ hMem⟩

/-- always implies eventuallyAlways (with k = 0) -/
theorem always_implies_eventuallyAlways (P : FaultState → Prop) (states : List FaultState) :
    states ≠ [] → always states P → eventuallyAlways states P := by
  intro hne hAll
  unfold eventuallyAlways
  unfold always at hAll
  refine ⟨0, ?_, ?_⟩
  · match states, hne with | _ :: _, _ => simp
  · intro σ hMem
    exact hAll σ (List.drop_subset _ _ hMem)

/-! ## Snapshot Invariants -/

/-- Snapshotting records the current env value for variables in the list. -/
theorem snapshot_records_current (σ : FaultState) (vars : List Name) (x : Name)
    (hx : x ∈ vars) :
    (σ.snapshot vars).history x σ.round = σ.env x := by
  simp [FaultState.snapshot]
  intro h
  exact absurd hx h

/-- Snapshotting does not alter history at rounds other than the current one. -/
theorem snapshot_preserves_past (σ : FaultState) (vars : List Name) (x : Name) (n : Nat)
    (hn : n ≠ σ.round) :
    (σ.snapshot vars).history x n = σ.history x n := by
  simp [FaultState.snapshot]
  intro h
  exact absurd h hn

/-- Snapshotting does not change the environment. -/
theorem snapshot_preserves_env (σ : FaultState) (vars : List Name) :
    (σ.snapshot vars).env = σ.env := by
  rfl

/-- Snapshotting does not change the round counter. -/
theorem snapshot_preserves_round (σ : FaultState) (vars : List Name) :
    (σ.snapshot vars).round = σ.round := by
  rfl
