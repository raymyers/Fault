/-
  FaultSemantics.State

  Semantic domains: FaultState and Labels for the LTS.
-/
import FaultSemantics.Syntax

/-! ## Semantic Values

  In the SMT encoding, all numerics become reals.
  We model this with a simplified semantic value type. -/

/-- Semantic values after evaluation (no unknown/uncertain — those become nondeterminism) -/
inductive SVal where
  | real : Float → SVal
  | bool : Bool → SVal
  | nil  : SVal
  deriving Repr, BEq, Inhabited

/-! ## Environment -/

/-- A variable environment mapping qualified names to semantic values -/
abbrev Env := Name → SVal

/-- The empty environment (everything is nil) -/
def Env.empty : Env := fun _ => SVal.nil

/-- Update a binding in the environment -/
def Env.update (σ : Env) (x : Name) (v : SVal) : Env :=
  fun y => if y == x then v else σ y

/-! ## Global State -/

/-- The complete state of a Fault model at a point in execution -/
structure FaultState where
  /-- Stock property values (the store) -/
  env       : Env
  /-- Current simulation round (0-indexed) -/
  round     : Nat
  /-- Component → current state name -/
  compState : Name → Name
  /-- Variable history: name → round → value (for [now-k] references) -/
  history   : Name → Nat → SVal
  deriving Inhabited

/-! ## Labels -/

/-- Labels for the Labeled Transition System.
    Each label represents an observable action. -/
inductive Label where
  /-- Internal / silent step -/
  | tau
  /-- A flow function was executed -/
  | flowExec (flowName funcName : Name)
  /-- A component entered a new state -/
  | stateEntry (compName stateName : Name)
  /-- A stock was modified -/
  | assign (varName : Name) (op : FlowOp) (val : SVal)
  /-- A conditional branch was taken -/
  | branch (taken : Bool)
  /-- A round boundary was crossed -/
  | round (n : Nat)
  deriving Repr, BEq, Inhabited

/-! ## State Operations -/

namespace FaultState

/-- Update a variable in the environment -/
def setVar (σ : FaultState) (x : Name) (v : SVal) : FaultState :=
  { σ with env := σ.env.update x v }

/-- Read a variable from the environment -/
def getVar (σ : FaultState) (x : Name) : SVal :=
  σ.env x

/-- Update a component's current state -/
def setCompState (σ : FaultState) (comp state : Name) : FaultState :=
  { σ with compState := fun c => if c == comp then state else σ.compState c }

/-- Snapshot current env into history at the current round -/
def snapshot (σ : FaultState) (vars : List Name) : FaultState :=
  { σ with history := fun x n =>
      if n == σ.round && vars.elem x then σ.env x
      else σ.history x n }

/-- Advance to the next round -/
def nextRound (σ : FaultState) : FaultState :=
  { σ with round := σ.round + 1 }

/-- Read a historical value: x[now - k] -/
def readHistory (σ : FaultState) (x : Name) (k : Int) : SVal :=
  let targetRound := (Int.ofNat σ.round) + k  -- k is typically negative
  if targetRound >= 0 then σ.history x targetRound.toNat
  else SVal.nil

/-- Initial state from a spec's stock definitions and constants -/
def init (stocks : List StockDef) (constants : List ConstDef)
    (startStates : List (Name × Name)) : FaultState where
  env := fun x =>
    -- Look up in stock properties first
    let fromStocks := stocks.findSome? fun s =>
      (s.props.find? fun (n, _) => n == x) |>.map fun (_, v) =>
        match v with
        | Val.nat n => SVal.real (Float.ofNat n)
        | Val.float f => SVal.real f
        | Val.bool b => SVal.bool b
        | _ => SVal.nil
    -- Then look up in constants
    let fromConsts := constants.findSome? fun c =>
      if c.name == x then
        match c.value with
        | Val.nat n => some (SVal.real (Float.ofNat n))
        | Val.float f => some (SVal.real f)
        | Val.bool b => some (SVal.bool b)
        | _ => some SVal.nil
      else none
    fromStocks.getD (fromConsts.getD SVal.nil)
  round := 0
  compState := fun c =>
    match startStates.find? (fun (comp, _) => comp == c) with
    | some (_, s) => s
    | none => ""
  history := fun _ _ => SVal.nil

end FaultState
