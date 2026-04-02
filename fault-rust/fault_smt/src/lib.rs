//! SMT-LIB2 code generation for the Fault language.
//!
//! Translates a resolved Fault program into QF_NRA (quantifier-free nonlinear
//! real arithmetic) constraints. Uses SSA-style variable versioning so each
//! assignment creates a new version: `var_0`, `var_1`, etc.
//!
//! Guided by `semantics/docs/implementation.md` §10 and the Go reference
//! compiler's `generator/rules/` module.

mod encode;
mod ssa;

pub use encode::encode_program;
