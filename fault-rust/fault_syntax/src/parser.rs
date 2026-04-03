//! Recursive-descent parser for the Fault language.
//!
//! Produces AST types defined in the parent crate from token streams.

use crate::lexer::{LexError, Lexer, Token, TokenKind};
use crate::*;
use std::fmt;

// ── Error type ──────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct ParseError {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.msg)
    }
}

impl std::error::Error for ParseError {}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> Self {
        ParseError {
            line: e.line,
            col: e.col,
            msg: e.msg,
        }
    }
}

// ── Public API ──────────────────────────────────────────────────────

/// Parse a `.fspec` source string into a [`Spec`].
pub fn parse_spec(src: &str) -> Result<Spec, ParseError> {
    let tokens = Lexer::new(src).tokenize()?;
    let mut p = Parser::new(tokens);
    p.parse_spec()
}

/// Parse a `.fsystem` source string into a [`System`].
pub fn parse_system(src: &str) -> Result<System, ParseError> {
    let tokens = Lexer::new(src).tokenize()?;
    let mut p = Parser::new(tokens);
    p.parse_system()
}

// ── Parser ──────────────────────────────────────────────────────────

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, pos: 0 }
    }

    // ── Token helpers ───────────────────────────────────────────────

    fn peek(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn kind(&self) -> TokenKind {
        self.peek().kind
    }

    fn advance(&mut self) -> &Token {
        let tok = &self.tokens[self.pos.min(self.tokens.len() - 1)];
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        if self.kind() == kind {
            Ok(self.advance().clone())
        } else {
            Err(self.error(format!("expected {:?}, got {:?}", kind, self.kind())))
        }
    }

    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.kind() == kind {
            self.advance();
            true
        } else {
            false
        }
    }

    fn eat_semi(&mut self) {
        // Semicolons are often optional at end of blocks
        self.eat(TokenKind::Semi);
    }

    fn error(&self, msg: String) -> ParseError {
        let tok = self.peek();
        ParseError {
            line: tok.line,
            col: tok.col,
            msg,
        }
    }

    // ── Spec parsing ────────────────────────────────────────────────

    fn parse_spec(&mut self) -> Result<Spec, ParseError> {
        self.expect(TokenKind::Spec)?;
        let name = self.expect(TokenKind::Ident)?.text;
        self.expect(TokenKind::Semi)?;

        let mut constants = Vec::new();
        let mut stocks = Vec::new();
        let mut flows = Vec::new();
        let mut invariants = Vec::new();
        let mut import_decls = Vec::new();
        let mut string_decls: Vec<(Name, Expr)> = Vec::new();

        loop {
            match self.kind() {
                TokenKind::Def => {
                    self.advance();
                    let def_name = self.expect(TokenKind::Ident)?.text;
                    self.expect(TokenKind::Assign)?;
                    match self.kind() {
                        TokenKind::Stock => {
                            stocks.push(self.parse_stock_def(def_name)?);
                        }
                        TokenKind::Flow => {
                            flows.push(self.parse_flow_def(def_name)?);
                        }
                        _ => {
                            return Err(
                                self.error("expected 'stock' or 'flow' after 'def name ='".into())
                            );
                        }
                    }
                    self.eat_semi();
                }
                TokenKind::Const => {
                    constants.extend(self.parse_const_decl()?);
                }
                TokenKind::Import => {
                    import_decls.push(self.parse_import_decl()?);
                }
                TokenKind::Assert => {
                    invariants.push(self.parse_assertion(false)?);
                }
                TokenKind::Assume => {
                    invariants.push(self.parse_assertion(true)?);
                }
                TokenKind::Ident => {
                    // String declaration: IDENT = string_expr ;
                    let sd = self.parse_string_decl()?;
                    string_decls.push(sd);
                }
                TokenKind::For | TokenKind::Eof => break,
                _ => {
                    return Err(self.error(format!("unexpected token in spec: {:?}", self.kind())));
                }
            }
        }

        let run_block = if self.kind() == TokenKind::For {
            Some(self.parse_for_stmt()?)
        } else {
            None
        };

        // Convert string decls into constants.
        // String literals → Bool(false), no expr (free Bool in SMT).
        // Boolean expressions referencing other strings → Bool(false) + expr.
        for (sname, sexpr) in string_decls {
            let is_literal = matches!(&sexpr, Expr::Lit(Val::Str(_)));
            constants.push(ConstDef {
                name: sname,
                value: Val::Bool(false),
                expr: if is_literal { None } else { Some(sexpr) },
            });
        }

        Ok(Spec {
            name,
            constants,
            stocks,
            flows,
            invariants,
            import_decls,
            imported_specs: Vec::new(),
            run_block,
        })
    }

    // ── System parsing ──────────────────────────────────────────────

    fn parse_system(&mut self) -> Result<System, ParseError> {
        self.expect(TokenKind::System)?;
        let name = self.expect(TokenKind::Ident)?.text;
        self.expect(TokenKind::Semi)?;

        let mut imports = Vec::new();
        let mut globals = Vec::new();
        let mut components = Vec::new();
        let mut invariants = Vec::new();
        let mut constants = Vec::new();
        let mut start_states = Vec::new();

        loop {
            match self.kind() {
                TokenKind::Import => {
                    imports.push(self.parse_import_decl()?);
                }
                TokenKind::Global => {
                    globals.push(self.parse_global_decl()?);
                }
                TokenKind::Component => {
                    components.push(self.parse_component_decl()?);
                }
                TokenKind::Const => {
                    constants.extend(self.parse_const_decl()?);
                }
                TokenKind::Assert => {
                    invariants.push(self.parse_assertion(false)?);
                }
                TokenKind::Assume => {
                    invariants.push(self.parse_assertion(true)?);
                }
                TokenKind::Start => {
                    start_states = self.parse_start_block()?;
                }
                TokenKind::Ident => {
                    // String decl in system context
                    self.parse_string_decl()?;
                }
                TokenKind::For | TokenKind::Eof => break,
                _ => {
                    return Err(
                        self.error(format!("unexpected token in system: {:?}", self.kind()))
                    );
                }
            }
        }

        let run_block = if self.kind() == TokenKind::For {
            Some(self.parse_for_stmt()?)
        } else {
            None
        };

        // Stub specs from import declarations (actual loading done later).
        let import_specs: Vec<Spec> = imports
            .iter()
            .map(|decl| Spec {
                name: decl.alias.clone(),
                constants: vec![],
                stocks: vec![],
                flows: vec![],
                invariants: vec![],
                import_decls: vec![],
                imported_specs: vec![],
                run_block: None,
            })
            .collect();

        Ok(System {
            name,
            imports: import_specs,
            import_decls: imports,
            globals,
            components,
            invariants,
            start_states,
            run_block,
        })
    }

    // ── Stock / Flow definitions ────────────────────────────────────

    fn parse_stock_def(&mut self, name: String) -> Result<StockDef, ParseError> {
        self.expect(TokenKind::Stock)?;
        self.expect(TokenKind::LBrace)?;

        let mut props = Vec::new();
        while self.kind() != TokenKind::RBrace {
            let prop_name = self.expect(TokenKind::Ident)?.text;
            if self.eat(TokenKind::Colon) {
                let val = self.parse_property_value()?;
                props.push((prop_name, val));
            } else {
                // Bare identifier = unknown
                props.push((prop_name, Val::Unknown));
            }
            self.eat(TokenKind::Comma);
        }
        self.expect(TokenKind::RBrace)?;

        Ok(StockDef { name, props })
    }

    fn parse_flow_def(&mut self, name: String) -> Result<FlowDef, ParseError> {
        self.expect(TokenKind::Flow)?;
        self.expect(TokenKind::LBrace)?;

        let mut stocks = Vec::new();
        let mut funcs = Vec::new();

        while self.kind() != TokenKind::RBrace {
            let prop_name = self.expect(TokenKind::Ident)?.text;
            self.expect(TokenKind::Colon)?;

            match self.kind() {
                TokenKind::Func => {
                    self.advance();
                    let body = self.parse_block()?;
                    funcs.push((prop_name, body));
                }
                TokenKind::New => {
                    self.advance();
                    let stock_name = self.parse_dotted_name()?;
                    stocks.push((prop_name, stock_name));
                }
                _ => {
                    // Other property values (bool, numeric, etc.) — store as stock-like property
                    let val = self.parse_property_value_from_current()?;
                    // Non-stock, non-func properties in flows become stock entries
                    // with a synthesized stock name
                    stocks.push((prop_name, format!("__val_{}", val_to_string(&val))));
                }
            }
            self.eat(TokenKind::Comma);
        }
        self.expect(TokenKind::RBrace)?;

        Ok(FlowDef {
            name,
            stocks,
            funcs,
        })
    }

    fn parse_property_value(&mut self) -> Result<Val, ParseError> {
        self.parse_property_value_from_current()
    }

    fn parse_property_value_from_current(&mut self) -> Result<Val, ParseError> {
        match self.kind() {
            TokenKind::IntLit => {
                let tok = self.advance().clone();
                Ok(parse_int_val(&tok.text))
            }
            TokenKind::Minus => {
                self.advance();
                let tok = self.advance().clone();
                match tok.kind {
                    TokenKind::IntLit => {
                        let n = parse_int_val(&tok.text);
                        match n {
                            Val::Nat(v) => Ok(Val::Float(-(v as f64))),
                            _ => Ok(n),
                        }
                    }
                    TokenKind::FloatLit => {
                        let f: f64 = tok.text.parse().unwrap_or(0.0);
                        Ok(Val::Float(-f))
                    }
                    _ => Err(self.error("expected number after '-'".into())),
                }
            }
            TokenKind::FloatLit => {
                let tok = self.advance().clone();
                let f: f64 = tok.text.parse().unwrap_or(0.0);
                Ok(Val::Float(f))
            }
            TokenKind::True => {
                self.advance();
                Ok(Val::Bool(true))
            }
            TokenKind::False => {
                self.advance();
                Ok(Val::Bool(false))
            }
            TokenKind::StringLit => {
                let tok = self.advance().clone();
                Ok(Val::Str(tok.text))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Val::Nil)
            }
            TokenKind::TyUnknown => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                self.expect(TokenKind::RParen)?;
                Ok(Val::Unknown)
            }
            TokenKind::TyUncertain => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let mean = self.parse_numeric_f64()?;
                self.expect(TokenKind::Comma)?;
                let sigma = self.parse_numeric_f64()?;
                self.expect(TokenKind::RParen)?;
                Ok(Val::Uncertain { mean, sigma })
            }
            _ => {
                // Try solvable types: string(), bool(), int(), float(), natural()
                if matches!(
                    self.kind(),
                    TokenKind::TyString
                        | TokenKind::TyBool
                        | TokenKind::TyInt
                        | TokenKind::TyFloat
                        | TokenKind::TyNatural
                ) {
                    self.advance();
                    self.expect(TokenKind::LParen)?;
                    // May have arguments
                    while self.kind() != TokenKind::RParen {
                        self.advance();
                        self.eat(TokenKind::Comma);
                    }
                    self.expect(TokenKind::RParen)?;
                    return Ok(Val::Unknown);
                }
                Err(self.error(format!("expected property value, got {:?}", self.kind())))
            }
        }
    }

    fn parse_numeric_f64(&mut self) -> Result<f64, ParseError> {
        let neg = self.eat(TokenKind::Minus);
        let tok = self.advance().clone();
        let val: f64 = match tok.kind {
            TokenKind::IntLit | TokenKind::FloatLit => tok.text.parse().unwrap_or(0.0),
            _ => return Err(self.error("expected number".into())),
        };
        Ok(if neg { -val } else { val })
    }

    // ── Block / statements ──────────────────────────────────────────

    fn parse_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();
        while self.kind() != TokenKind::RBrace {
            let stmt = self.parse_statement()?;
            stmts.push(stmt);
        }
        self.expect(TokenKind::RBrace)?;
        Ok(stmts)
    }

    fn parse_statement(&mut self) -> Result<Stmt, ParseError> {
        match self.kind() {
            TokenKind::If => self.parse_if_stmt(),
            _ => {
                let stmt = self.parse_simple_stmt()?;
                self.eat_semi();
                Ok(stmt)
            }
        }
    }

    fn parse_simple_stmt(&mut self) -> Result<Stmt, ParseError> {
        // Parse LHS expression, then check for assignment operator
        let lhs = self.parse_expression()?;

        match self.kind() {
            TokenKind::Assign => {
                self.advance();
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&lhs);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Assign,
                    expr: rhs,
                })
            }
            TokenKind::BackArrow => {
                self.advance();
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&lhs);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Inflow,
                    expr: rhs,
                })
            }
            TokenKind::Arrow => {
                self.advance();
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&lhs);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Outflow,
                    expr: rhs,
                })
            }
            // Compound assignment: +=, -=, etc. (expr op= expr)
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::Caret
            | TokenKind::Lshift
            | TokenKind::Rshift
            | TokenKind::Amp
            | TokenKind::BitClear
                if self.tokens.get(self.pos + 1).map(|t| t.kind) == Some(TokenKind::Assign)
                    || (self.pos + 1 < self.tokens.len()
                        && self.tokens[self.pos].kind == self.kind()) =>
            {
                // Not commonly used in Fault, but grammar allows it
                let _op_tok = self.advance().clone();
                self.expect(TokenKind::Assign)?;
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&lhs);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Assign,
                    expr: rhs,
                })
            }
            _ => {
                // Expression statement — could be a function call like `l.fn`
                expr_to_stmt(lhs)
            }
        }
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.expect(TokenKind::If)?;
        let cond = self.parse_expression()?;
        let then_branch = self.parse_block()?;
        let else_branch = if self.eat(TokenKind::Else) {
            if self.kind() == TokenKind::If {
                vec![self.parse_if_stmt()?]
            } else {
                self.parse_block()?
            }
        } else {
            vec![]
        };
        Ok(Stmt::IfThenElse {
            cond,
            then_branch,
            else_branch,
        })
    }

    // ── Expressions (precedence climbing) ───────────────────────────

    fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_or_expr()
    }

    fn parse_or_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and_expr()?;
        while self.kind() == TokenKind::Or {
            self.advance();
            let right = self.parse_and_expr()?;
            left = Expr::BinOp {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_and_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison_expr()?;
        while self.kind() == TokenKind::And {
            self.advance();
            let right = self.parse_comparison_expr()?;
            left = Expr::BinOp {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_comparison_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_add_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::Eq => BinOp::Eq,
                TokenKind::Neq => BinOp::Neq,
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Le => BinOp::Le,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::Ge => BinOp::Ge,
                _ => break,
            };
            self.advance();
            let right = self.parse_add_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_add_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_mul_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::Plus => BinOp::Add,
                TokenKind::Minus => BinOp::Sub,
                TokenKind::Caret => BinOp::BitXor,
                _ => break,
            };
            self.advance();
            let right = self.parse_mul_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_mul_expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_expo_expr()?;
        loop {
            let op = match self.kind() {
                TokenKind::Star => BinOp::Mul,
                TokenKind::Slash => BinOp::Div,
                TokenKind::Percent => BinOp::Mod,
                TokenKind::Lshift => BinOp::Lshift,
                TokenKind::Rshift => BinOp::Rshift,
                TokenKind::Amp => BinOp::BitAnd,
                TokenKind::BitClear => BinOp::BitClear,
                _ => break,
            };
            self.advance();
            let right = self.parse_expo_expr()?;
            left = Expr::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_expo_expr(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_unary_expr()?;
        if self.kind() == TokenKind::Expo {
            self.advance();
            let right = self.parse_expo_expr()?; // right-associative
            Ok(Expr::BinOp {
                op: BinOp::Exp,
                left: Box::new(left),
                right: Box::new(right),
            })
        } else {
            Ok(left)
        }
    }

    fn parse_unary_expr(&mut self) -> Result<Expr, ParseError> {
        match self.kind() {
            TokenKind::Bang => {
                self.advance();
                let expr = self.parse_unary_expr()?;
                Ok(Expr::UnOp {
                    op: UnOp::Not,
                    expr: Box::new(expr),
                })
            }
            TokenKind::Minus => {
                // Check if this is a negative number literal or unary minus
                let next_kind = self.tokens.get(self.pos + 1).map(|t| t.kind);
                if matches!(next_kind, Some(TokenKind::IntLit | TokenKind::FloatLit)) {
                    // Could be negative literal, but we treat as unary minus for expressions
                    self.advance();
                    let expr = self.parse_unary_expr()?;
                    Ok(Expr::UnOp {
                        op: UnOp::Neg,
                        expr: Box::new(expr),
                    })
                } else {
                    self.advance();
                    let expr = self.parse_unary_expr()?;
                    Ok(Expr::UnOp {
                        op: UnOp::Neg,
                        expr: Box::new(expr),
                    })
                }
            }
            TokenKind::Plus | TokenKind::Star | TokenKind::Amp => {
                // Prefix operators from grammar (rarely used)
                self.advance();
                self.parse_unary_expr()
            }
            _ => self.parse_postfix_expr(),
        }
    }

    fn parse_postfix_expr(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            match self.kind() {
                TokenKind::Dot => {
                    self.advance();
                    let field = self.expect(TokenKind::Ident)?.text;
                    expr = Expr::Dot {
                        expr: Box::new(expr),
                        field,
                    };
                }
                TokenKind::LBracket => {
                    // Index/History access: name[expr]
                    self.advance();
                    let index_expr = self.parse_expression()?;
                    self.expect(TokenKind::RBracket)?;
                    let name = expr_to_name(&expr);
                    if is_absolute_index(&index_expr) {
                        let idx = eval_history_offset(&index_expr) as u64;
                        expr = Expr::Index { name, index: idx };
                    } else {
                        let offset = eval_history_offset(&index_expr);
                        expr = Expr::History { name, offset };
                    }
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn parse_primary_expr(&mut self) -> Result<Expr, ParseError> {
        match self.kind() {
            TokenKind::IntLit => {
                let tok = self.advance().clone();
                let val = parse_int_val(&tok.text);
                Ok(Expr::Lit(val))
            }
            TokenKind::FloatLit => {
                let tok = self.advance().clone();
                let f: f64 = tok.text.parse().unwrap_or(0.0);
                Ok(Expr::Lit(Val::Float(f)))
            }
            TokenKind::True => {
                self.advance();
                Ok(Expr::Lit(Val::Bool(true)))
            }
            TokenKind::False => {
                self.advance();
                Ok(Expr::Lit(Val::Bool(false)))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Expr::Lit(Val::Nil))
            }
            TokenKind::StringLit => {
                let tok = self.advance().clone();
                Ok(Expr::Lit(Val::Str(tok.text)))
            }
            TokenKind::Ident => {
                let tok = self.advance().clone();
                Ok(Expr::Var(tok.text))
            }
            TokenKind::This => {
                self.advance();
                Ok(Expr::Var("this".into()))
            }
            TokenKind::Now => {
                self.advance();
                Ok(Expr::Var("now".into()))
            }
            TokenKind::LParen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(TokenKind::RParen)?;
                Ok(expr)
            }
            // Solvable types as expressions: unknown(), uncertain(m,s), etc.
            TokenKind::TyUnknown => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                self.expect(TokenKind::RParen)?;
                Ok(Expr::Lit(Val::Unknown))
            }
            TokenKind::TyUncertain => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let mean = self.parse_numeric_f64()?;
                self.expect(TokenKind::Comma)?;
                let sigma = self.parse_numeric_f64()?;
                self.expect(TokenKind::RParen)?;
                Ok(Expr::Lit(Val::Uncertain { mean, sigma }))
            }
            TokenKind::TyString
            | TokenKind::TyBool
            | TokenKind::TyInt
            | TokenKind::TyFloat
            | TokenKind::TyNatural => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let mut _args = Vec::new();
                while self.kind() != TokenKind::RParen {
                    _args.push(self.parse_expression()?);
                    self.eat(TokenKind::Comma);
                }
                self.expect(TokenKind::RParen)?;
                Ok(Expr::Lit(Val::Unknown))
            }
            // State machine builtins
            TokenKind::Advance => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let target = self.parse_dotted_name()?;
                self.expect(TokenKind::RParen)?;
                // Return as a pseudo-expression; converted to Stmt later
                Ok(Expr::Var(format!("__advance_{}", target)))
            }
            TokenKind::Stay => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                self.expect(TokenKind::RParen)?;
                Ok(Expr::Var("__stay".into()))
            }
            TokenKind::Leave => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                if self.kind() != TokenKind::RParen {
                    let _target = self.parse_dotted_name()?;
                }
                self.expect(TokenKind::RParen)?;
                Ok(Expr::Var("__leave".into()))
            }
            TokenKind::Choose => {
                self.advance();
                // "choose" is followed by a bool expression
                let expr = self.parse_expression()?;
                Ok(expr)
            }
            _ => Err(self.error(format!(
                "expected expression, got {:?} '{}'",
                self.kind(),
                self.peek().text,
            ))),
        }
    }

    // ── For / Init / Run ────────────────────────────────────────────

    fn parse_for_stmt(&mut self) -> Result<(u64, Vec<Stmt>, Vec<Stmt>), ParseError> {
        self.expect(TokenKind::For)?;
        let rounds = self.parse_int_literal()?;

        let init_block = if self.eat(TokenKind::Init) {
            self.parse_init_block()?
        } else {
            vec![]
        };

        self.expect(TokenKind::Run)?;
        let run_block = self.parse_run_block()?;

        self.eat_semi();

        Ok((rounds, init_block, run_block))
    }

    fn parse_init_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();

        while self.kind() != TokenKind::RBrace {
            // Could be: IDENT = new TYPE ; (init step)
            //       or: paramCall = expr ; (swap)
            let saved = self.pos;
            let name_parts = self.parse_dotted_name_raw()?;

            if self.kind() == TokenKind::Assign {
                self.advance();
                if self.kind() == TokenKind::New {
                    // Init step: name = new type ;
                    self.advance();
                    let type_name = self.parse_dotted_name()?;
                    self.eat_semi();
                    stmts.push(Stmt::FlowAssign {
                        name: name_parts.join("."),
                        op: FlowOp::Assign,
                        expr: Expr::Var(format!("new {}", type_name)),
                    });
                } else {
                    // Swap: name.prop = value ;
                    let expr = self.parse_expression()?;
                    self.eat_semi();
                    stmts.push(Stmt::FlowAssign {
                        name: name_parts.join("."),
                        op: FlowOp::Assign,
                        expr,
                    });
                }
            } else {
                // Not an assignment — backtrack and stop
                self.pos = saved;
                break;
            }
        }
        self.expect(TokenKind::RBrace)?;

        Ok(stmts)
    }

    fn parse_run_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();

        while self.kind() != TokenKind::RBrace {
            match self.kind() {
                TokenKind::If => {
                    stmts.push(self.parse_if_run_stmt()?);
                }
                _ => {
                    let step = self.parse_run_step()?;
                    stmts.push(step);
                    self.eat_semi();
                }
            }
        }
        self.expect(TokenKind::RBrace)?;

        Ok(stmts)
    }

    fn parse_run_step(&mut self) -> Result<Stmt, ParseError> {
        // Parse first expression (typically a paramCall like l.fn)
        let first = self.parse_expression()?;

        // Check for parallel: expr | expr | ...
        if self.kind() == TokenKind::Pipe {
            let mut parts = vec![expr_to_stmt(first)?];
            while self.eat(TokenKind::Pipe) {
                let next = self.parse_expression()?;
                parts.push(expr_to_stmt(next)?);
            }
            return Ok(Stmt::Parallel(parts));
        }

        // Check for assignment operators
        match self.kind() {
            TokenKind::Assign => {
                self.advance();
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&first);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Assign,
                    expr: rhs,
                })
            }
            TokenKind::BackArrow => {
                self.advance();
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&first);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Inflow,
                    expr: rhs,
                })
            }
            TokenKind::Arrow => {
                self.advance();
                let rhs = self.parse_expression()?;
                let name = expr_to_name(&first);
                Ok(Stmt::FlowAssign {
                    name,
                    op: FlowOp::Outflow,
                    expr: rhs,
                })
            }
            _ => expr_to_stmt(first),
        }
    }

    fn parse_if_run_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.expect(TokenKind::If)?;
        let cond = self.parse_expression()?;
        let then_block = self.parse_run_block()?;
        let else_block = if self.eat(TokenKind::Else) {
            if self.kind() == TokenKind::If {
                vec![self.parse_if_run_stmt()?]
            } else {
                self.parse_run_block()?
            }
        } else {
            vec![]
        };
        Ok(Stmt::IfThenElse {
            cond,
            then_branch: then_block,
            else_branch: else_block,
        })
    }

    // ── Assertions / Invariants ─────────────────────────────────────

    fn parse_assertion(&mut self, is_assume: bool) -> Result<Invariant, ParseError> {
        self.advance(); // consume 'assert' or 'assume'

        // Check for 'when ... then ...'
        if self.kind() == TokenKind::When {
            self.advance();
            let guard = self.parse_expression()?;
            self.expect(TokenKind::Then)?;
            let body = self.parse_expression()?;
            let temporal = self.parse_optional_temporal()?;
            self.eat_semi();

            return Ok(if is_assume {
                Invariant::AssumeWhen {
                    guard,
                    body,
                    temporal,
                }
            } else {
                Invariant::AssertWhen {
                    guard,
                    body,
                    temporal,
                }
            });
        }

        // Parse invariant expression
        let expr = self.parse_expression()?;

        // Check if this is `operand = expression` style invariant
        let expr = if self.kind() == TokenKind::Assign {
            self.advance();
            let rhs = self.parse_expression()?;
            Expr::BinOp {
                op: BinOp::Eq,
                left: Box::new(expr),
                right: Box::new(rhs),
            }
        } else {
            expr
        };

        let temporal = self.parse_optional_temporal()?;
        self.eat_semi();

        Ok(if is_assume {
            Invariant::Assume { expr, temporal }
        } else {
            Invariant::Assert { expr, temporal }
        })
    }

    fn parse_optional_temporal(&mut self) -> Result<Temporal, ParseError> {
        match self.kind() {
            TokenKind::Always => {
                self.advance();
                Ok(Temporal::Always)
            }
            TokenKind::Eventually => {
                self.advance();
                Ok(Temporal::Eventually)
            }
            TokenKind::EventuallyAlways => {
                self.advance();
                Ok(Temporal::EventuallyAlways)
            }
            TokenKind::Nmt => {
                self.advance();
                let n = self.parse_int_literal()?;
                Ok(Temporal::Nmt(n))
            }
            TokenKind::Nft => {
                self.advance();
                let n = self.parse_int_literal()?;
                Ok(Temporal::Nft(n))
            }
            _ => Ok(Temporal::Always), // default
        }
    }

    // ── Constants ───────────────────────────────────────────────────

    fn parse_const_decl(&mut self) -> Result<Vec<ConstDef>, ParseError> {
        self.expect(TokenKind::Const)?;
        let mut consts = Vec::new();

        if self.eat(TokenKind::LParen) {
            while self.kind() != TokenKind::RParen {
                let name = self.parse_dotted_name()?;
                if self.eat(TokenKind::Assign) {
                    let val = self.parse_property_value()?;
                    consts.push(ConstDef {
                        name,
                        value: val,
                        expr: None,
                    });
                } else {
                    consts.push(ConstDef {
                        name,
                        value: Val::Unknown,
                        expr: None,
                    });
                }
                self.eat_semi();
            }
            self.expect(TokenKind::RParen)?;
        } else {
            let name = self.parse_dotted_name()?;
            if self.eat(TokenKind::Assign) {
                let val = self.parse_property_value()?;
                consts.push(ConstDef {
                    name,
                    value: val,
                    expr: None,
                });
            } else {
                consts.push(ConstDef {
                    name,
                    value: Val::Unknown,
                    expr: None,
                });
            }
        }
        self.eat_semi();

        Ok(consts)
    }

    // ── Imports ─────────────────────────────────────────────────────

    fn parse_import_decl(&mut self) -> Result<ImportDecl, ParseError> {
        self.expect(TokenKind::Import)?;

        let mut alias = String::new();
        let mut path = String::new();

        if self.eat(TokenKind::LParen) {
            // Grouped: import (alias "path") or import ("path")
            while self.kind() != TokenKind::RParen {
                if self.kind() == TokenKind::Ident || self.kind() == TokenKind::Dot {
                    alias = self.advance().text.clone();
                }
                if self.kind() == TokenKind::StringLit {
                    path = self.advance().text.clone();
                }
                self.eat(TokenKind::Comma);
                self.eat_semi();
            }
            self.expect(TokenKind::RParen)?;
        } else {
            // Bare: import alias "path" or import "path"
            if self.kind() == TokenKind::Ident {
                let next = self.tokens.get(self.pos + 1).map(|t| t.kind);
                if next == Some(TokenKind::StringLit) {
                    alias = self.advance().text.clone();
                }
            }
            if self.kind() == TokenKind::StringLit {
                path = self.advance().text.clone();
            }
        }
        self.eat_semi();

        // Default alias = spec name derived from filename
        if alias.is_empty() {
            alias = path
                .rsplit('/')
                .next()
                .unwrap_or(&path)
                .trim_end_matches(".fspec")
                .trim_end_matches(".fsystem")
                .to_string();
        }

        Ok(ImportDecl { alias, path })
    }

    // ── System-specific ─────────────────────────────────────────────

    fn parse_global_decl(&mut self) -> Result<GlobalDecl, ParseError> {
        self.expect(TokenKind::Global)?;
        let name = self.expect(TokenKind::Ident)?.text;
        self.expect(TokenKind::Assign)?;

        let type_name = if self.eat(TokenKind::New) {
            self.parse_dotted_name()?
        } else {
            let expr = self.parse_expression()?;
            format!("{:?}", expr)
        };
        self.eat_semi();

        // Parse optional property swaps
        let mut swaps = Vec::new();
        while self.kind() == TokenKind::Ident || self.kind() == TokenKind::This {
            let saved = self.pos;
            let swap_parts = self.parse_dotted_name_raw()?;
            if self.kind() == TokenKind::Assign {
                self.advance();
                let rhs = self.parse_expression()?;
                self.eat_semi();
                swaps.push((swap_parts.join("."), rhs));
            } else {
                self.pos = saved;
                break;
            }
        }

        Ok(GlobalDecl {
            name,
            type_name,
            swaps,
        })
    }

    fn parse_component_decl(&mut self) -> Result<CompDef, ParseError> {
        self.expect(TokenKind::Component)?;
        let name = self.expect(TokenKind::Ident)?.text;
        self.expect(TokenKind::Assign)?;
        self.expect(TokenKind::States)?;
        self.expect(TokenKind::LBrace)?;

        let mut states = Vec::new();
        while self.kind() != TokenKind::RBrace {
            let state_name = self.expect(TokenKind::Ident)?.text;
            self.expect(TokenKind::Colon)?;
            self.expect(TokenKind::Func)?;
            let body = self.parse_state_block()?;
            states.push((state_name, body));
            self.eat(TokenKind::Comma);
        }
        self.expect(TokenKind::RBrace)?;
        self.eat_semi();

        Ok(CompDef { name, states })
    }

    fn parse_state_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();

        while self.kind() != TokenKind::RBrace {
            match self.kind() {
                TokenKind::If => {
                    stmts.push(self.parse_if_state_stmt()?);
                }
                TokenKind::Choose => {
                    self.advance();
                    let expr = self.parse_expression()?;
                    self.eat_semi();
                    stmts.push(Stmt::ChooseTransition(expr));
                }
                _ => {
                    // Parse a full expression — handles advance(), stay(), leave(),
                    // paramCall, and compound boolean expressions like
                    // advance(a) || advance(b) && advance(c)
                    let first = self.parse_expression()?;
                    if self.kind() == TokenKind::Pipe {
                        let mut parts = vec![expr_to_stmt(first)?];
                        while self.eat(TokenKind::Pipe) {
                            let next = self.parse_expression()?;
                            parts.push(expr_to_stmt(next)?);
                        }
                        self.eat_semi();
                        stmts.push(Stmt::Parallel(parts));
                    } else {
                        self.eat_semi();
                        stmts.push(expr_to_stmt(first)?);
                    }
                }
            }
        }
        self.expect(TokenKind::RBrace)?;

        Ok(stmts)
    }

    fn parse_if_state_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.expect(TokenKind::If)?;
        let cond = self.parse_expression()?;
        let then_block = self.parse_state_block()?;
        let else_block = if self.eat(TokenKind::Else) {
            if self.kind() == TokenKind::If {
                vec![self.parse_if_state_stmt()?]
            } else {
                self.parse_state_block()?
            }
        } else {
            vec![]
        };
        Ok(Stmt::IfThenElse {
            cond,
            then_branch: then_block,
            else_branch: else_block,
        })
    }

    fn parse_start_block(&mut self) -> Result<Vec<(Name, Name)>, ParseError> {
        self.expect(TokenKind::Start)?;
        self.expect(TokenKind::LBrace)?;

        let mut pairs = Vec::new();
        while self.kind() != TokenKind::RBrace {
            let comp = self.expect(TokenKind::Ident)?.text;
            self.expect(TokenKind::Colon)?;
            let state = self.expect(TokenKind::Ident)?.text;
            pairs.push((comp, state));
            self.eat(TokenKind::Comma);
        }
        self.expect(TokenKind::RBrace)?;
        self.eat_semi();

        Ok(pairs)
    }

    // ── String declarations ─────────────────────────────────────────

    fn parse_string_decl(&mut self) -> Result<(Name, Expr), ParseError> {
        let name = self.expect(TokenKind::Ident)?.text;
        self.expect(TokenKind::Assign)?;
        let expr = self.parse_expression()?;
        self.eat_semi();
        Ok((name, expr))
    }

    // ── Helpers ─────────────────────────────────────────────────────

    fn parse_dotted_name(&mut self) -> Result<String, ParseError> {
        let parts = self.parse_dotted_name_raw()?;
        Ok(parts.join("."))
    }

    fn parse_dotted_name_raw(&mut self) -> Result<Vec<String>, ParseError> {
        let mut parts = Vec::new();
        let first = if self.kind() == TokenKind::This {
            self.advance();
            "this".to_string()
        } else {
            self.expect(TokenKind::Ident)?.text
        };
        parts.push(first);

        while self.kind() == TokenKind::Dot {
            self.advance();
            let part = self.expect(TokenKind::Ident)?.text;
            parts.push(part);
        }

        Ok(parts)
    }

    fn parse_int_literal(&mut self) -> Result<u64, ParseError> {
        let tok = self.advance().clone();
        match tok.kind {
            TokenKind::IntLit => parse_int_text(&tok.text).ok_or_else(|| ParseError {
                line: tok.line,
                col: tok.col,
                msg: format!("invalid integer: {}", tok.text),
            }),
            _ => Err(ParseError {
                line: tok.line,
                col: tok.col,
                msg: format!("expected integer, got {:?}", tok.kind),
            }),
        }
    }
}

// ── Free helper functions ───────────────────────────────────────────

fn parse_int_text(s: &str) -> Option<u64> {
    if s.starts_with("0x") || s.starts_with("0X") {
        u64::from_str_radix(&s[2..], 16).ok()
    } else if s.starts_with('0') && s.len() > 1 && s.chars().all(|c| c.is_ascii_digit()) {
        u64::from_str_radix(s, 8).ok()
    } else {
        s.parse().ok()
    }
}

fn parse_int_val(s: &str) -> Val {
    if let Some(n) = parse_int_text(s) {
        Val::Nat(n)
    } else {
        Val::Nat(0)
    }
}

fn val_to_string(v: &Val) -> String {
    match v {
        Val::Nat(n) => n.to_string(),
        Val::Float(f) => f.to_string(),
        Val::Bool(b) => b.to_string(),
        Val::Str(s) => s.clone(),
        Val::Unknown => "unknown".into(),
        Val::Uncertain { mean, sigma } => format!("uncertain({},{})", mean, sigma),
        Val::Nil => "nil".into(),
    }
}

/// Convert an expression to a flat name string (for assignment LHS).
fn expr_to_name(expr: &Expr) -> String {
    match expr {
        Expr::Var(n) => n.clone(),
        Expr::Dot { expr, field } => {
            let base = expr_to_name(expr);
            format!("{}.{}", base, field)
        }
        _ => format!("{:?}", expr),
    }
}

/// Convert an expression to a statement (for function calls, advance, stay).
fn expr_to_stmt(expr: Expr) -> Result<Stmt, ParseError> {
    match &expr {
        Expr::Var(name) if name.starts_with("__advance_") => {
            let target = name.strip_prefix("__advance_").unwrap().to_string();
            Ok(Stmt::Advance(target))
        }
        Expr::Var(name) if name == "__stay" => Ok(Stmt::Stay),
        Expr::Var(name) if name == "__leave" => Ok(Stmt::Stay),
        Expr::Var(name) => Ok(Stmt::Call(name.clone())),
        Expr::Dot { .. } => {
            let name = expr_to_name(&expr);
            Ok(Stmt::Call(name))
        }
        // Compound state transitions: advance(X) && advance(Y), advance(X) || advance(Y)
        Expr::BinOp { .. } if expr_contains_state_op(&expr) => {
            Ok(Stmt::CompoundTransition(expr))
        }
        _ => Ok(Stmt::Call(format!("{:?}", expr))),
    }
}

/// Check if an expression contains advance() or stay() pseudo-vars.
fn expr_contains_state_op(expr: &Expr) -> bool {
    match expr {
        Expr::Var(name) => name.starts_with("__advance_") || name == "__stay",
        Expr::BinOp { left, right, .. } => {
            expr_contains_state_op(left) || expr_contains_state_op(right)
        }
        _ => false,
    }
}

/// Check if an index expression is absolute (bare integer, no `now`).
fn is_absolute_index(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(Val::Nat(_)))
}

/// Evaluate a history index expression to an offset.
/// `now - k` → `-k`, `now + k` → `k`, bare integer `n` → `n`
fn eval_history_offset(expr: &Expr) -> i64 {
    match expr {
        Expr::Lit(Val::Nat(n)) => *n as i64,
        Expr::BinOp {
            op: BinOp::Sub,
            left,
            right,
        } => {
            let l = eval_history_offset(left);
            let r = eval_history_offset(right);
            l - r
        }
        Expr::BinOp {
            op: BinOp::Add,
            left,
            right,
        } => {
            let l = eval_history_offset(left);
            let r = eval_history_offset(right);
            l + r
        }
        Expr::Var(name) if name == "now" => 0,
        Expr::UnOp {
            op: UnOp::Neg,
            expr,
        } => -eval_history_offset(expr),
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_spec() {
        let src = r#"spec simple;

def st = stock{
    value: 30,
};

def fl = flow{
    vault: new st,
    fn: func{
        if vault.value > 4 {
           vault.value <- vault.value - 2;
        }
    },
};

for 1 init{l = new fl;} run {
    l.fn;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "simple");
        assert_eq!(spec.stocks.len(), 1);
        assert_eq!(spec.stocks[0].name, "st");
        assert_eq!(spec.stocks[0].props, vec![("value".into(), Val::Nat(30))]);
        assert_eq!(spec.flows.len(), 1);
        assert_eq!(spec.flows[0].name, "fl");
        assert!(spec.run_block.is_some());
        let (rounds, _init, _run) = spec.run_block.as_ref().unwrap();
        assert_eq!(*rounds, 1);
    }

    #[test]
    fn parse_bathtub_parallel() {
        let src = r#"spec bathtub;

def faucet = flow{
    water: new tub,
    in: func{
        water.level <- 10;
    },
};

def drain = flow{
    water: new tub,
    out: func{
        water.level -> 20;
    },
};

def tub = stock{
    level: 5,
};

for 4 init{drawn = new faucet;
    pipe = new drain;} run {
    drawn.in | pipe.out;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "bathtub");
        assert_eq!(spec.stocks.len(), 1);
        assert_eq!(spec.flows.len(), 2);
        let (rounds, init, run) = spec.run_block.as_ref().unwrap();
        assert_eq!(*rounds, 4);
        assert_eq!(init.len(), 2);
        // Run block should have a Parallel statement
        assert_eq!(run.len(), 1);
        assert!(matches!(&run[0], Stmt::Parallel(_)));
    }

    #[test]
    fn parse_assertions() {
        let src = r#"spec asserts;

def fsample = flow{
    target: new ssample,
    fn: func{
        target.value -> target.value/2;
    },
};

def ssample = stock{
    value: 40,
};

assert ssample.value == 40;
assume fsample.target.value > 2;

for 4 init{test = new fsample;} run {
    test.fn;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "asserts");
        assert_eq!(spec.invariants.len(), 2);
        assert!(matches!(&spec.invariants[0], Invariant::Assert { .. }));
        assert!(matches!(&spec.invariants[1], Invariant::Assume { .. }));
    }

    #[test]
    fn parse_history_ref() {
        let src = r#"spec history1;

def counter = flow{
    value: 1,
    step: func{
        if this.value > 0 {
            this.value <- this.value[now-1];
        } else {
            this.value = 1;
        }
    }
};

for 4 init{c = new counter;} run{
    c.step;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "history1");
        assert_eq!(spec.flows.len(), 1);
        // The flow has a "value" property (not a stock ref, not a func)
        // and a "step" func
        assert_eq!(spec.flows[0].funcs.len(), 1);
    }

    #[test]
    fn parse_unknowns() {
        let src = r#"spec unknowns;

def s = stock{
    a,
    b: 2,
    c: 0,
};

def f = flow{
    data: new s,
    fn: func{
       data.c <- data.a + data.b;
    },
};

assume s.a > 5;
assert s.a <= 6;

for 3 init{loop = new f;} run {
    loop.fn;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "unknowns");
        assert_eq!(spec.stocks[0].props.len(), 3);
        // First prop 'a' should be Unknown (bare identifier)
        assert_eq!(spec.stocks[0].props[0], ("a".into(), Val::Unknown));
        assert_eq!(spec.stocks[0].props[1], ("b".into(), Val::Nat(2)));
        assert_eq!(spec.stocks[0].props[2], ("c".into(), Val::Nat(0)));
    }

    #[test]
    fn parse_booleans() {
        let src = r#"spec booleans;

def st = stock{
    value: true,
};

def fl = flow{
    vault: new st,
    fn: func{
        if vault.value {
            vault.value = false;
        }else{
            vault.value = true;
        }
    },
};

for 1 init{l = new fl;} run {
    l.fn;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "booleans");
        assert_eq!(spec.stocks[0].props[0].1, Val::Bool(true));
    }

    #[test]
    fn parse_system_statechart() {
        let src = r#"system statechart;

import simple "../simpleA.fspec";

global fl = new simple.fl;

component drain = states{
    initial: func{
        if !fl.active {
            advance(this.open);
        }
    },
    open: func{
        if fl.vault.value < 0 {
            advance(this.close);
        }
    },
    close: func{
        stay();
    },
};

start {
    drain: initial,
};

for 2 run {
    if !drain.close{
        fl.fn;
    }
}"#;
        let sys = parse_system(src).unwrap();
        assert_eq!(sys.name, "statechart");
        assert_eq!(sys.components.len(), 1);
        assert_eq!(sys.components[0].name, "drain");
        assert_eq!(sys.components[0].states.len(), 3);
        assert_eq!(sys.start_states, vec![("drain".into(), "initial".into())]);
    }

    #[test]
    fn parse_strings_spec() {
        let src = r#"spec test;
str1 = "is a fish";
str2 = "tastes delicious with ginger";
str3 = "native to North America";
str4 = !str1 && str2;

assume (str1 && str3) || str4;
assert str3;"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "test");
        assert_eq!(spec.invariants.len(), 2);
    }

    #[test]
    fn parse_indexes() {
        let src = r#"spec indexes;

def foo = stock{
    a: 10,
};

def bar = flow{
    bash: new foo,
    fizz: func{
        bash.a <- bash.a[0] - 2;
    },
};

for 2 init{
    gee = new bar;
}run{
    gee.fizz;
};"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "indexes");
        assert_eq!(spec.flows[0].funcs.len(), 1);
    }

    #[test]
    fn parse_multicond() {
        let src = r#"spec multicond;

def s = stock{
    cond: 1,
    value: 10,
};

def f = flow{
    base: new s,
    change: func{
        if base.cond > 0 {
            base.value <- 10;
            base.cond <- 2;
        }
        if base.cond > 4{
            base.value <- 20;
            base.cond -> 2;
        }
    },
};

for 1 init{t = new f;} run {
    t.change;
};"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "multicond");
        // The change func should have 2 if statements
        let body = &spec.flows[0].funcs[0].1;
        assert_eq!(body.len(), 2);
    }

    #[test]
    fn parse_increment_with_history() {
        let src = r#"spec increment;

def fib = flow{
    value: 0,
    step: func{
        if this.value == 0 {
              this.value = 1;
        }else{
              this.value <- this.value[now-1];
        }
    }
};

for 5 init{f = new fib;} run{
    f.step;
}"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.name, "increment");
        assert_eq!(spec.flows[0].funcs.len(), 1);
        let (rounds, _, _) = spec.run_block.as_ref().unwrap();
        assert_eq!(*rounds, 5);
    }

    #[test]
    fn parse_bare_const() {
        let src = r#"spec cache;
const table;
const memory;
const limit = 100;
"#;
        let spec = parse_spec(src).unwrap();
        assert_eq!(spec.constants.len(), 3);
        assert_eq!(spec.constants[0].name, "table");
        assert_eq!(spec.constants[0].value, Val::Unknown);
        assert_eq!(spec.constants[1].name, "memory");
        assert_eq!(spec.constants[1].value, Val::Unknown);
        assert_eq!(spec.constants[2].name, "limit");
        assert_eq!(spec.constants[2].value, Val::Nat(100));
    }
}
