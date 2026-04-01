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
    For unknown/uncertain values, this returns nil — nondeterminism
    is handled at the transition level. -/
def eval (σ : FaultState) : Expr → SVal
  | .lit (.nat n)   => .real (Float.ofNat n)
  | .lit (.float f) => .real f
  | .lit (.bool b)  => .bool b
  | .lit _          => .nil
  | .var x          => σ.getVar x
  | .binop op l r   => evalBinOp op (eval σ l) (eval σ r)
  | .unop op e      => evalUnOp op (eval σ e)
  | .dot e _field   => eval σ e  -- simplified: treat dot access as variable lookup
  | .history x k    => σ.readHistory x k
  | .choose _       => .nil      -- nondeterministic: resolved at transition level

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
    `faultStep σ μ σ'` means state σ transitions to σ' emitting label μ. -/
inductive faultStep : FaultState → Label → FaultState → Prop where
  /-- Stock assignment: stock op= expr -/
  | assignStep (σ : FaultState) (x : Name) (op : FlowOp) (e : Expr) :
      faultStep σ
        (.assign x op (eval σ e))
        (σ.setVar x (applyFlowOp op (σ.getVar x) (eval σ e)))

  /-- Conditional: true branch -/
  | ifTrue (σ : FaultState) (cond : Expr) (thenBody elseBody : List Stmt) :
      eval σ cond = .bool true →
      faultStep σ (.branch true) σ

  /-- Conditional: false branch -/
  | ifFalse (σ : FaultState) (cond : Expr) (thenBody elseBody : List Stmt) :
      eval σ cond = .bool false →
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
