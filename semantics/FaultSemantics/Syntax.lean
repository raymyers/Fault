/-
  FaultSemantics.Syntax

  Abstract syntax of the Fault modeling language.
  Source of truth: ast/ast.go in the Go compiler.
-/

/-- Variable / identifier names -/
abbrev Name := String

/-! ## Values -/

/-- Runtime values in the Fault language.
    All numerics are reals in the SMT encoding (QF_NRA). -/
inductive Val where
  | nat   : Nat → Val
  | float : Float → Val
  | bool  : Bool → Val
  | str   : String → Val           -- string literal (compiles to bool false in Go)
  | unknown                         -- solver-determined free variable
  | uncertain (mean sigma : Float)  -- normal distribution N(μ,σ)
  | nil
  deriving Repr, BEq, Inhabited

/-! ## Operators -/

/-- Binary operators -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | lt | le | gt | ge
  | and | or
  | lshift | rshift
  | bitAnd | bitOr | bitXor | bitClear
  deriving Repr, BEq

/-- Unary operators -/
inductive UnOp where
  | neg | not
  deriving Repr, BEq

/-- Stock flow operators: the three assignment forms in Fault flows -/
inductive FlowOp where
  | assign   -- `=`   reset value
  | inflow   -- `←`   increment (stock <- expr)
  | outflow  -- `→`   decrement (stock -> expr)
  deriving Repr, BEq

/-! ## Expressions -/

/-- Fault expressions -/
inductive Expr where
  | lit     : Val → Expr
  | var     : Name → Expr
  | binop   : BinOp → Expr → Expr → Expr
  | unop    : UnOp → Expr → Expr
  | dot     : Expr → Name → Expr            -- e.field (ParameterCall)
  | history : Name → Int → Expr             -- x[now - k]
  | choose  : List Expr → Expr              -- nondeterministic choice (||)
  deriving Repr, BEq, Inhabited

/-! ## Statements -/

/-- Fault statements -/
inductive Stmt where
  | flowAssign : Name → FlowOp → Expr → Stmt  -- stock op expr
  | ifThenElse : Expr → List Stmt → List Stmt → Stmt
  | call       : Name → Stmt                   -- invoke a flow function
  | advance    : Name → Stmt                   -- state transition
  | stay       : Stmt                           -- remain in current state
  | seq        : List Stmt → Stmt               -- sequential composition
  | parallel   : List Stmt → Stmt               -- concurrent (|) composition
  deriving Repr, BEq

/-! ## Temporal modalities for assertions -/

/-- Temporal operators used in assert/assume statements -/
inductive Temporal where
  | always                  -- □  (default)
  | eventually              -- ◇
  | eventuallyAlways        -- ◇□
  | nmt : Nat → Temporal    -- no more than n times
  | nft : Nat → Temporal    -- no fewer than n times
  deriving Repr, BEq

/-! ## Invariants -/

/-- An invariant is an assertion or assumption with a temporal modality -/
inductive Invariant where
  | assert : Expr → Temporal → Invariant
  | assume : Expr → Temporal → Invariant
  /-- `when guard then body` — conditional assertion/assumption.
      Go compiler: generates `(=> guard body)` for assume,
      `(and guard (not body))` for assert (negated). -/
  | assertWhen : Expr → Expr → Temporal → Invariant
  | assumeWhen : Expr → Expr → Temporal → Invariant
  deriving Repr, BEq

/-! ## Declarations -/

/-- Stock definition: a named collection of property-value pairs -/
structure StockDef where
  name  : Name
  props : List (Name × Val)
  deriving Repr, BEq

/-- Flow definition: named, with stock instances and named functions -/
structure FlowDef where
  name   : Name
  stocks : List (Name × Name)        -- local name → stock type name
  funcs  : List (Name × List Stmt)   -- function name → body
  deriving Repr, BEq

/-- Component definition: state machine with named states -/
structure CompDef where
  name   : Name
  states : List (Name × List Stmt)   -- state name → state function body
  deriving Repr, BEq

/-- A constant declaration -/
structure ConstDef where
  name  : Name
  value : Val
  deriving Repr, BEq

/-! ## Top-level structures -/

/-- A .fspec file -/
structure Spec where
  name       : Name
  constants  : List ConstDef
  stocks     : List StockDef
  flows      : List FlowDef
  invariants : List Invariant
  runBlock   : Option (Nat × List Stmt × List Stmt)  -- (rounds, init, run)
  deriving Repr

/-- A .fsystem file -/
structure System where
  name        : Name
  imports     : List Spec
  components  : List CompDef
  invariants  : List Invariant
  startStates : List (Name × Name)                   -- component → initial state
  runBlock    : Option (Nat × List Stmt × List Stmt)  -- (rounds, init, run)
  deriving Repr
