/-
  FaultSemantics.Temporal

  Phase 4: Assertion and temporal semantics over bounded traces.
  Defines how Fault's temporal operators (always, eventually,
  eventually-always, nmt, nft) are interpreted over finite
  execution traces, and how assertions/assumptions constrain
  the model checking problem.
-/
import FaultSemantics.Execution

/-! ## Bounded Temporal Operators

  These match the SMT encodings in generator/asserts/asserts.go. -/

/-- `always P states` — P holds at every state in the trace.
    SMT: `(and P₀ P₁ ... Pₙ)` -/
def always (states : List FaultState) (P : FaultState → Prop) : Prop :=
  ∀ σ ∈ states, P σ

/-- `eventually P states` — P holds at some state in the trace.
    SMT: `(or P₀ P₁ ... Pₙ)` -/
def eventually (states : List FaultState) (P : FaultState → Prop) : Prop :=
  ∃ σ ∈ states, P σ

/-- `eventuallyAlways P states` — there exists a point k after which P always holds.
    SMT: `(or (Pₙ) (P_{n-1} ∧ Pₙ) ... (P₀ ∧ ... ∧ Pₙ))` -/
def eventuallyAlways (states : List FaultState) (P : FaultState → Prop) : Prop :=
  ∃ k, k < states.length ∧
    ∀ σ ∈ states.drop k, P σ

/-- `noMoreThan n P states` — P holds at most n times.
    SMT: combinatorial constraint (asserts.go:484) -/
def noMoreThan (states : List FaultState) (P : FaultState → Prop) (n : Nat) : Prop :=
  ∀ l, l ⊆ states → (∀ σ ∈ l, P σ) → l.length ≤ n

/-- `noFewerThan n P states` — P holds at least n times.
    SMT: `(or ⋁_{S ∈ C(N,n)} ⋀_{i∈S} Pᵢ)` -/
def noFewerThan (states : List FaultState) (P : FaultState → Prop) (n : Nat) : Prop :=
  ∃ l, l ⊆ states ∧ (∀ σ ∈ l, P σ) ∧ l.length ≥ n

/-! ## Temporal Operator Interpretation -/

/-- Interpret a Fault temporal operator as a predicate over a state trace -/
def interpretTemporal (temp : Temporal) (P : FaultState → Prop)
    (states : List FaultState) : Prop :=
  match temp with
  | .always           => always states P
  | .eventually       => eventually states P
  | .eventuallyAlways => eventuallyAlways states P
  | .nmt n            => noMoreThan states P n
  | .nft n            => noFewerThan states P n

/-! ## Expression to State Predicate -/

/-- Convert a Fault expression to a state predicate via evaluation.
    The expression is "true" when it evaluates to `SVal.bool true`. -/
def exprPredicate (e : Expr) : FaultState → Prop :=
  fun σ => eval σ e = .bool true

/-! ## Assertion Semantics -/

/-- An assertion holds over a trace when the temporal property is satisfied.
    `assertionHolds` is the positive form: the assertion is valid. -/
def assertionHolds (e : Expr) (temp : Temporal)
    (states : List FaultState) : Prop :=
  interpretTemporal temp (exprPredicate e) states

/-- An assertion is violated when the negation is satisfiable.
    This is what the Fault compiler actually checks via SMT. -/
def assertionViolated (e : Expr) (temp : Temporal)
    (states : List FaultState) : Prop :=
  ¬ assertionHolds e temp states

/-- An assumption constrains the trace space (not negated).
    Only traces satisfying the assumption are considered. -/
def assumptionHolds (e : Expr) (temp : Temporal)
    (states : List FaultState) : Prop :=
  interpretTemporal temp (exprPredicate e) states

/-! ## Invariant Checking -/

/-- Check an invariant against a trace -/
def checkInvariant (inv : Invariant) (states : List FaultState) : Prop :=
  match inv with
  | .assert e temp => assertionHolds e temp states
  | .assume e temp => assumptionHolds e temp states

/-- All invariants hold over a trace -/
def allInvariantsHold (invs : List Invariant) (states : List FaultState) : Prop :=
  ∀ inv ∈ invs, checkInvariant inv states

/-! ## Model Checking Problem -/

/-- The Fault model checking problem:
    Given a set of assumptions and assertions, find a trace where
    all assumptions hold but some assertion is violated. -/
structure ModelCheckQuery where
  assumptions : List (Expr × Temporal)
  assertions  : List (Expr × Temporal)

/-- A counterexample is a trace that satisfies all assumptions
    but violates at least one assertion -/
def isCounterexample (q : ModelCheckQuery) (states : List FaultState) : Prop :=
  (∀ p ∈ q.assumptions, assumptionHolds p.1 p.2 states) ∧
  (∃ p ∈ q.assertions, assertionViolated p.1 p.2 states)

/-- A model is correct when no counterexample exists -/
def modelCorrect (q : ModelCheckQuery) : Prop :=
  ∀ states : List FaultState, ¬ isCounterexample q states

/-! ## Key Theorems -/

/-- The negation of `always P` is `eventually (¬P)` -/
theorem not_always_iff_eventually_not (P : FaultState → Prop) (states : List FaultState) :
    ¬ always states P ↔ eventually states (fun σ => ¬ P σ) := by
  unfold always eventually
  push Not
  rfl

/-- The negation of `eventually P` is `always (¬P)` -/
theorem not_eventually_iff_always_not (P : FaultState → Prop) (states : List FaultState) :
    ¬ eventually states P ↔ always states (fun σ => ¬ P σ) := by
  unfold always eventually
  push Not
  rfl

/-- `noFewerThan 1` is equivalent to `eventually` -/
theorem nft_one_iff_eventually (P : FaultState → Prop) (states : List FaultState) :
    noFewerThan states P 1 ↔ eventually states P := by
  sorry  -- To be proved

/-- `noMoreThan 0` is equivalent to `always (¬P)` -/
theorem nmt_zero_iff_always_not (P : FaultState → Prop) (states : List FaultState) :
    noMoreThan states P 0 ↔ always states (fun σ => ¬ P σ) := by
  sorry  -- To be proved
