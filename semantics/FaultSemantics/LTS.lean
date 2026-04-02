/-
  FaultSemantics.LTS

  The Fault operational semantics as a Labeled Transition System
  using CSLib's LTS framework.
-/
import Cslib.Foundations.Semantics.LTS.Basic
import FaultSemantics.State

open Cslib

/-! ## Expression Evaluation -/

/-- Evaluate a binary operation on semantic values -/
def evalBinOp (op : BinOp) (l r : SVal) : SVal :=
  match op, l, r with
  -- Arithmetic on reals
  | .add, .real a, .real b => .real (a + b)
  | .sub, .real a, .real b => .real (a - b)
  | .mul, .real a, .real b => .real (a * b)
  | .div, .real a, .real b => .real (a / b)
  -- Comparisons on reals
  | .eq,  .real a, .real b => .bool (a == b)
  | .neq, .real a, .real b => .bool (a != b)
  | .lt,  .real a, .real b => .bool (a < b)
  | .le,  .real a, .real b => .bool (a ≤ b)
  | .gt,  .real a, .real b => .bool (a > b)
  | .ge,  .real a, .real b => .bool (a ≥ b)
  -- Boolean operations
  | .and, .bool a, .bool b => .bool (a && b)
  | .or,  .bool a, .bool b => .bool (a || b)
  -- Equality on booleans
  | .eq,  .bool a, .bool b => .bool (a == b)
  | .neq, .bool a, .bool b => .bool (a != b)
  | _, _, _ => .nil

/-- Evaluate a unary operation -/
def evalUnOp (op : UnOp) (v : SVal) : SVal :=
  match op, v with
  | .neg, .real a => .real (-a)
  | .not, .bool a => .bool (!a)
  | _, _ => .nil

/-- Deterministic expression evaluation against a state.
    For concrete values, this is the primary evaluation function.
    For unknown/uncertain, returns .nil — use `EvalR` (relational)
    for reasoning about nondeterministic values. -/
def eval (σ : FaultState) : Expr → SVal
  | .lit (.nat n)   => .real (Float.ofNat n)
  | .lit (.float f) => .real f
  | .lit (.bool b)  => .bool b
  | .lit (.str _)   => .bool false  -- Go compiler: strings compile to `false`
  | .lit _          => .nil
  | .var x          => σ.getVar x
  | .binop op l r   => evalBinOp op (eval σ l) (eval σ r)
  | .unop op e      => evalUnOp op (eval σ e)
  | .dot e _field   => eval σ e  -- pre-flattened names: dot should be resolved before execution
  | .history x k    => σ.readHistory x k
  | .choose _       => .nil      -- nondeterministic: resolved at transition level

/-! ## Relational Evaluation (for unknown/uncertain)

  The Go compiler treats `unknown()` as a free SMT variable — the solver
  can assign ANY value. `uncertain(μ,σ)` is also free (any real value,
  with probability annotation post-hoc).

  `EvalR σ e v` means "expression `e` CAN evaluate to value `v` in state `σ`."
  For concrete values, this coincides with `eval`. For unknowns, ANY value works.
-/

/-- Relational expression evaluation: `EvalR σ e v` holds when `e` can
    evaluate to `v` in state `σ`. This is the authoritative semantics
    for nondeterministic values. -/
inductive EvalR : FaultState → Expr → SVal → Prop where
  | litNat (σ : FaultState) (n : Nat) :
      EvalR σ (.lit (.nat n)) (.real (Float.ofNat n))
  | litFloat (σ : FaultState) (f : Float) :
      EvalR σ (.lit (.float f)) (.real f)
  | litBool (σ : FaultState) (b : Bool) :
      EvalR σ (.lit (.bool b)) (.bool b)
  | litStr (σ : FaultState) (s : String) :
      EvalR σ (.lit (.str s)) (.bool false)
  /-- Unknown: can be ANY value. This is the key nondeterminism rule.
      The SMT solver is free to choose any satisfying value. -/
  | litUnknown (σ : FaultState) (v : SVal) :
      EvalR σ (.lit .unknown) v
  /-- Uncertain: can be any real value (probability annotated post-hoc) -/
  | litUncertain (σ : FaultState) (μ σ_ : Float) (v : Float) :
      EvalR σ (.lit (.uncertain μ σ_)) (.real v)
  | var (σ : FaultState) (x : Name) :
      EvalR σ (.var x) (σ.getVar x)
  | binop (σ : FaultState) (op : BinOp) (l r : Expr) (vl vr : SVal) :
      EvalR σ l vl → EvalR σ r vr →
      EvalR σ (.binop op l r) (evalBinOp op vl vr)
  | unop (σ : FaultState) (op : UnOp) (e : Expr) (v : SVal) :
      EvalR σ e v →
      EvalR σ (.unop op e) (evalUnOp op v)
  | dot (σ : FaultState) (e : Expr) (field : Name) (v : SVal) :
      EvalR σ e v →
      EvalR σ (.dot e field) v
  | history (σ : FaultState) (x : Name) (k : Int) :
      EvalR σ (.history x k) (σ.readHistory x k)
  /-- Choose: nondeterministic selection from alternatives -/
  | choose (σ : FaultState) (es : List Expr) (e : Expr) (v : SVal) :
      e ∈ es → EvalR σ e v →
      EvalR σ (.choose es) v

/-- For concrete (non-unknown/uncertain) expressions, EvalR agrees with eval -/
theorem evalR_of_eval (σ : FaultState) (e : Expr) (v : SVal) :
    eval σ e = v → v ≠ .nil →
    EvalR σ e v := by
  sorry  -- provable by structural induction on e

/-! ## Arithmetic Helpers -/

/-- Apply a flow operation to a current value -/
def applyFlowOp (op : FlowOp) (current new_ : SVal) : SVal :=
  match op with
  | .assign  => new_
  | .inflow  =>
    match current, new_ with
    | .real a, .real b => .real (a + b)
    | _, _ => new_
  | .outflow =>
    match current, new_ with
    | .real a, .real b => .real (a - b)
    | _, _ => new_

/-! ## Small-Step Transition Relation -/

/-- The small-step transition relation for Fault.
    `faultStep σ μ σ'` means state σ transitions to σ' emitting label μ.

    Uses `EvalR` (relational evaluation) so that unknown/uncertain values
    generate nondeterministic transitions — the LTS contains ALL possible
    traces, matching what the SMT solver explores. -/
inductive faultStep : FaultState → Label → FaultState → Prop where
  /-- Stock assignment: stock op= expr.
      Uses EvalR so unknowns can take any value. -/
  | assignStep (σ : FaultState) (x : Name) (op : FlowOp) (e : Expr) (v : SVal) :
      EvalR σ e v →
      faultStep σ
        (.assign x op v)
        (σ.setVar x (applyFlowOp op (σ.getVar x) v))

  /-- Conditional: true branch.
      Uses EvalR so unknown conditions can go either way. -/
  | ifTrue (σ : FaultState) (cond : Expr) (thenBody elseBody : List Stmt) :
      EvalR σ cond (.bool true) →
      faultStep σ (.branch true) σ

  /-- Conditional: false branch -/
  | ifFalse (σ : FaultState) (cond : Expr) (thenBody elseBody : List Stmt) :
      EvalR σ cond (.bool false) →
      faultStep σ (.branch false) σ

  /-- Component state advance -/
  | advanceStep (σ : FaultState) (comp newState : Name) :
      faultStep σ (.stateEntry comp newState) (σ.setCompState comp newState)

  /-- Stay in current state (silent step) -/
  | stayStep (σ : FaultState) :
      faultStep σ .tau σ

  /-- Round boundary: snapshot history and advance round counter -/
  | roundStep (σ : FaultState) (vars : List Name) :
      faultStep σ
        (.round σ.round)
        ((σ.snapshot vars).nextRound)

/-! ## LTS Instantiation -/

/-- The Fault LTS using CSLib's framework -/
def FaultLTS : LTS FaultState Label where
  Tr := faultStep
