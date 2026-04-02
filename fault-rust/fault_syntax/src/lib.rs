//! AST types and parser for the Fault modeling language.
//!
//! Mirrors the formal definitions in `semantics/FaultSemantics/Syntax.lean`.

pub mod lexer;
pub mod parser;

use serde::{Deserialize, Serialize};

/// Variable / identifier names.
pub type Name = String;

// ── Values (Syntax.lean:15) ─────────────────────────────────────────

/// Runtime values in the Fault language.
/// All numerics are reals in the SMT encoding (QF_NRA).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Val {
    Nat(u64),
    Float(f64),
    Bool(bool),
    /// String literal — compiles to `Bool(false)` in the Go compiler.
    Str(String),
    /// Solver-determined free variable.
    Unknown,
    /// Normal distribution N(mean, sigma).
    Uncertain {
        mean: f64,
        sigma: f64,
    },
    Nil,
}

// ── Operators (Syntax.lean:28–46) ───────────────────────────────────

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Exp,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Lshift,
    Rshift,
    BitAnd,
    BitOr,
    BitXor,
    BitClear,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnOp {
    Neg,
    Not,
}

/// Stock flow operators: the three assignment forms in Fault flows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FlowOp {
    /// `=`  — reset value
    Assign,
    /// `←`  — increment (stock <- expr)
    Inflow,
    /// `→`  — decrement (stock -> expr)
    Outflow,
}

// ── Expressions (Syntax.lean:51) ────────────────────────────────────

/// Fault expressions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Lit(Val),
    Var(Name),
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    UnOp {
        op: UnOp,
        expr: Box<Expr>,
    },
    /// Property access `e.field` — resolved away before execution.
    Dot {
        expr: Box<Expr>,
        field: Name,
    },
    /// Temporal reference `name[now + offset]`.
    History {
        name: Name,
        offset: i64,
    },
    /// Nondeterministic choice (`||`).
    Choose(Vec<Expr>),
}

// ── Statements (Syntax.lean:64) ─────────────────────────────────────

/// Fault statements.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Stmt {
    FlowAssign {
        name: Name,
        op: FlowOp,
        expr: Expr,
    },
    IfThenElse {
        cond: Expr,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
    },
    /// Invoke a flow function.
    Call(Name),
    /// State machine transition.
    Advance(Name),
    /// Remain in current state.
    Stay,
    /// Sequential composition.
    Seq(Vec<Stmt>),
    /// Concurrent (`|`) composition.
    Parallel(Vec<Stmt>),
}

// ── Temporal modalities (Syntax.lean:77) ────────────────────────────

/// Temporal operators used in assert/assume statements.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Temporal {
    Always,
    Eventually,
    EventuallyAlways,
    /// No more than n times.
    Nmt(u64),
    /// No fewer than n times.
    Nft(u64),
}

// ── Invariants (Syntax.lean:88) ─────────────────────────────────────

/// An invariant is an assertion or assumption with a temporal modality.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Invariant {
    Assert {
        expr: Expr,
        temporal: Temporal,
    },
    Assume {
        expr: Expr,
        temporal: Temporal,
    },
    /// `when guard then body` — conditional assertion.
    AssertWhen {
        guard: Expr,
        body: Expr,
        temporal: Temporal,
    },
    /// `when guard then body` — conditional assumption.
    AssumeWhen {
        guard: Expr,
        body: Expr,
        temporal: Temporal,
    },
}

// ── Declarations (Syntax.lean:100–124) ──────────────────────────────

/// Stock definition: a named collection of property-value pairs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StockDef {
    pub name: Name,
    pub props: Vec<(Name, Val)>,
}

/// Flow definition: named, with stock instances and named functions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FlowDef {
    pub name: Name,
    /// Local name → stock type name.
    pub stocks: Vec<(Name, Name)>,
    /// Function name → body.
    pub funcs: Vec<(Name, Vec<Stmt>)>,
}

/// Component definition: state machine with named states.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CompDef {
    pub name: Name,
    /// State name → state function body.
    pub states: Vec<(Name, Vec<Stmt>)>,
}

/// A constant declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConstDef {
    pub name: Name,
    pub value: Val,
}

// ── Top-level structures (Syntax.lean:128–145) ──────────────────────

/// A `.fspec` file.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Spec {
    pub name: Name,
    pub constants: Vec<ConstDef>,
    pub stocks: Vec<StockDef>,
    pub flows: Vec<FlowDef>,
    pub invariants: Vec<Invariant>,
    /// (rounds, init_block, run_block)
    pub run_block: Option<(u64, Vec<Stmt>, Vec<Stmt>)>,
}

/// A `.fsystem` file.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct System {
    pub name: Name,
    pub imports: Vec<Spec>,
    pub components: Vec<CompDef>,
    pub invariants: Vec<Invariant>,
    /// Component name → initial state name.
    pub start_states: Vec<(Name, Name)>,
    /// (rounds, init_block, run_block)
    pub run_block: Option<(u64, Vec<Stmt>, Vec<Stmt>)>,
}

#[cfg(test)]
mod tests;
