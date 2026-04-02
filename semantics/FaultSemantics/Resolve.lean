/-
  FaultSemantics.Resolve

  Phase 8.1, 8.7, 8.8: Name resolution, import merging, and alias resolution.

  The Go compiler flattens all qualified names to underscore-delimited strings
  during preprocessing. For example, in spec "myspec" with scope "mybuffer":
    f.target.value → myspec_mybuffer_f_target_value

  The execution semantics (LTS, ExecStmt, etc.) operate on pre-flattened names.
  This module defines the flattening functions so an implementer can apply them
  during parsing/preprocessing.
-/
import FaultSemantics.Syntax

/-! ## Name Flattening -/

/-- Join a list of name parts with underscore separators.
    This is the Go compiler's `IdString()` function:
    `strings.Join(rawid, "_")` -/
def flattenName (parts : List Name) : Name :=
  parts.intersperse "_" |>.foldl (· ++ ·) ""

#guard flattenName ["myspec", "mybuffer", "f", "target", "value"]
  == "myspec_mybuffer_f_target_value"
#guard flattenName ["simple", "l", "vault", "value"]
  == "simple_l_vault_value"
#guard flattenName ["x"] == "x"

/-! ## Alias Resolution (Stock Swaps)

  The Go compiler's `AliasToBaseRaw` recursively resolves name aliases
  created by stock swaps. An alias maps one flat name to another.
  Resolution is recursive: if A → B and B → C, then A resolves to C.
-/

/-- An alias map from flat names to flat names -/
abbrev AliasMap := Name → Option Name

/-- The empty alias map -/
def AliasMap.empty : AliasMap := fun _ => none

/-- Add an alias mapping -/
def AliasMap.insert (m : AliasMap) (from_ to_ : Name) : AliasMap :=
  fun x => if x == from_ then some to_ else m x

/-- Resolve an alias recursively (with fuel to prevent infinite loops).
    Matches Go's `AliasToBaseRaw` which recursively calls itself. -/
def resolveAlias (aliases : AliasMap) (name : Name) (fuel : Nat := 100) : Name :=
  match fuel with
  | 0 => name
  | fuel' + 1 =>
    match aliases name with
    | some resolved => resolveAlias aliases resolved fuel'
    | none => name

/-! ## Expression Resolution

  Replace `Expr.dot` nodes with flat `Expr.var` nodes.
  In the Go compiler, dot notation is resolved during preprocessing
  by the `compileParameterCall` function (llvm/compiler.go:651-701).

  After resolution, all property accesses are flat variable names.
-/

/-- Resolve a dot expression to a flat variable name.
    `scope` is the current context path (spec name, flow instance, etc.) -/
partial def resolveExpr (aliases : AliasMap) (scope : List Name) : Expr → Expr
  | .dot e field =>
    -- Recursively resolve the base, then append the field
    let base := resolveExpr aliases scope e
    match base with
    | .var x => .var (resolveAlias aliases (x ++ "_" ++ field))
    | _ => .var (resolveAlias aliases (flattenName (scope ++ [field])))
  | .var x => .var (resolveAlias aliases x)
  | .binop op l r => .binop op (resolveExpr aliases scope l) (resolveExpr aliases scope r)
  | .unop op e => .unop op (resolveExpr aliases scope e)
  | .history x k => .history (resolveAlias aliases x) k
  | .choose es => .choose (es.map (resolveExpr aliases scope))
  | e => e  -- lit: no resolution needed

/-- Resolve all expressions in a statement -/
partial def resolveStmt (aliases : AliasMap) (scope : List Name) : Stmt → Stmt
  | .flowAssign x op e => .flowAssign (resolveAlias aliases x) op (resolveExpr aliases scope e)
  | .ifThenElse c t f => .ifThenElse (resolveExpr aliases scope c)
      (t.map (resolveStmt aliases scope)) (f.map (resolveStmt aliases scope))
  | .call n => .call n
  | .advance n => .advance n
  | .stay => .stay
  | .seq ss => .seq (ss.map (resolveStmt aliases scope))
  | .parallel ss => .parallel (ss.map (resolveStmt aliases scope))

/-! ## Import Resolution

  The Go compiler merges imported .fspec files into the .fsystem's namespace:
  - Only stocks, flows, and constants are imported (not run blocks or assertions)
  - Imported names are prefixed with the import alias
  - This happens during preprocessing, before execution

  For the execution semantics, imports are resolved by:
  1. Collecting all stock definitions from imported specs
  2. Collecting all flow definitions from imported specs
  3. Collecting all constants from imported specs
  4. Building the initial FaultState from the merged definitions
-/

/-- Merge imported specs into a flat list of stock definitions -/
def mergeStocks (specs : List Spec) : List StockDef :=
  specs.flatMap fun s => s.stocks

/-- Merge imported constants -/
def mergeConstants (specs : List Spec) : List ConstDef :=
  specs.flatMap fun s => s.constants

/-- Merge imported flows -/
def mergeFlows (specs : List Spec) : List FlowDef :=
  specs.flatMap fun s => s.flows

/-- Merge imported invariants (assumptions only — assertions from imports are kept) -/
def mergeInvariants (specs : List Spec) : List Invariant :=
  specs.flatMap fun s => s.invariants

/-! ## Component Well-Formedness (Phase 8.9)

  In the Go compiler, component state functions are compiled as separate
  LLVM functions. They can only:
  - Call advance() or stay()
  - Evaluate conditions (if/then/else)
  - Trigger flow functions via call
  They CANNOT directly assign to stock properties (flowAssign).
-/

/-- A statement is valid inside a component state function -/
partial def validInStateFunc : Stmt → Bool
  | .advance _ => true
  | .stay => true
  | .call _ => true
  | .ifThenElse _ t f => t.all validInStateFunc && f.all validInStateFunc
  | .seq ss => ss.all validInStateFunc
  | .parallel ss => ss.all validInStateFunc
  | .flowAssign _ _ _ => false  -- NOT allowed in state functions

/-- A component definition is well-formed if all state functions
    contain only valid statements -/
def CompDef.wellFormed (c : CompDef) : Bool :=
  c.states.all fun (_, body) => body.all validInStateFunc

/-! ## Full Program Structure

  A complete Fault program ready for execution, after all preprocessing:
  - Names are flattened
  - Aliases are resolved
  - Imports are merged
  - Components are validated
-/

/-- A fully resolved program ready for execution -/
structure ResolvedProgram where
  /-- All stock definitions (from spec + imports) -/
  stocks     : List StockDef
  /-- All flow definitions (from spec + imports) -/
  flows      : List FlowDef
  /-- All constants (from spec + imports) -/
  constants  : List ConstDef
  /-- Component definitions (from .fsystem only) -/
  components : List CompDef
  /-- All invariants (assertions + assumptions) -/
  invariants : List Invariant
  /-- Initial component states -/
  startStates : List (Name × Name)
  /-- Number of rounds -/
  rounds     : Nat
  /-- Init block (runs once before round 0) -/
  initBlock  : List Stmt
  /-- Run block (runs every round) -/
  runBlock   : List Stmt
  /-- All variable names (for history snapshots) -/
  varNames   : List Name
  deriving Repr

/-- Build a ResolvedProgram from a Spec -/
def Spec.resolve (s : Spec) : ResolvedProgram where
  stocks := s.stocks
  flows := s.flows
  constants := s.constants
  components := []
  invariants := s.invariants
  startStates := []
  rounds := match s.runBlock with | some (n, _, _) => n | none => 0
  initBlock := match s.runBlock with | some (_, init, _) => init | none => []
  runBlock := match s.runBlock with | some (_, _, run) => run | none => []
  varNames := s.stocks.flatMap fun st => st.props.map fun (n, _) => n

/-- Build a ResolvedProgram from a System with imported Specs -/
def System.resolve (sys : System) : ResolvedProgram where
  stocks := mergeStocks sys.imports
  flows := mergeFlows sys.imports
  constants := mergeConstants sys.imports
  components := sys.components
  invariants := sys.invariants ++ mergeInvariants sys.imports
  startStates := sys.startStates
  rounds := match sys.runBlock with | some (n, _, _) => n | none => 0
  initBlock := match sys.runBlock with | some (_, init, _) => init | none => []
  runBlock := match sys.runBlock with | some (_, _, run) => run | none => []
  varNames := (mergeStocks sys.imports).flatMap fun st => st.props.map fun (n, _) => n
