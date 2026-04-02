//! Lexer for the Fault language.
//!
//! Tokenizes `.fspec` and `.fsystem` source text into a stream of [`Token`]s.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    // ── Keywords ───────────────────────────────────────
    Spec,
    System,
    Def,
    Const,
    Import,
    Stock,
    Flow,
    Func,
    For,
    Init,
    Run,
    New,
    If,
    Else,
    Assert,
    Assume,
    When,
    Then,
    Component,
    Start,
    States,
    Global,
    Advance,
    Stay,
    Leave,
    Choose,
    This,
    Now,
    Return,
    // Temporal keywords
    Eventually,
    EventuallyAlways,
    Always,
    Nmt,
    Nft,
    // Literal keywords
    True,
    False,
    Nil,
    // Type keywords
    TyString,
    TyBool,
    TyInt,
    TyFloat,
    TyNatural,
    TyUncertain,
    TyUnknown,

    // ── Literals ───────────────────────────────────────
    Ident,
    IntLit,
    FloatLit,
    StringLit,

    // ── Punctuation ────────────────────────────────────
    Semi,       // ;
    Colon,      // :
    Comma,      // ,
    Dot,        // .
    LParen,     // (
    RParen,     // )
    LBrace,     // {
    RBrace,     // }
    LBracket,   // [
    RBracket,   // ]
    PlusPlus,   // ++
    MinusMinus, // --

    // ── Operators ──────────────────────────────────────
    Plus,     // +
    Minus,    // -
    Star,     // *
    Expo,     // **
    Slash,    // /
    Percent,  // %
    Caret,    // ^
    Amp,      // &
    Bang,     // !
    Pipe,     // |
    Lshift,   // <<
    Rshift,   // >>
    BitClear, // &^

    // Comparison
    Eq,  // ==
    Neq, // !=
    Lt,  // <
    Le,  // <=
    Gt,  // >
    Ge,  // >=

    // Logical
    And, // &&
    Or,  // ||

    // Assignment
    Assign,    // =
    Arrow,     // ->
    BackArrow, // <-

    // ── Special ────────────────────────────────────────
    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub line: usize,
    pub col: usize,
}

impl Token {
    pub fn eof(line: usize, col: usize) -> Self {
        Token {
            kind: TokenKind::Eof,
            text: String::new(),
            line,
            col,
        }
    }
}

pub struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            src: src.as_bytes(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    pub fn tokenize(&mut self) -> Result<Vec<Token>, LexError> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token()?;
            let is_eof = tok.kind == TokenKind::Eof;
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        Ok(tokens)
    }

    fn peek(&self) -> u8 {
        if self.pos < self.src.len() {
            self.src[self.pos]
        } else {
            0
        }
    }

    fn peek_at(&self, offset: usize) -> u8 {
        let i = self.pos + offset;
        if i < self.src.len() { self.src[i] } else { 0 }
    }

    fn advance(&mut self) -> u8 {
        let ch = self.peek();
        if ch == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        self.pos += 1;
        ch
    }

    fn at_end(&self) -> bool {
        self.pos >= self.src.len()
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace (spaces, tabs, newlines)
            while !self.at_end() && matches!(self.peek(), b' ' | b'\t' | b'\r' | b'\n') {
                self.advance();
            }
            // Skip line comments
            if self.peek() == b'/' && self.peek_at(1) == b'/' {
                while !self.at_end() && self.peek() != b'\n' {
                    self.advance();
                }
                continue;
            }
            // Skip block comments
            if self.peek() == b'/' && self.peek_at(1) == b'*' {
                self.advance();
                self.advance();
                loop {
                    if self.at_end() {
                        break;
                    }
                    if self.peek() == b'*' && self.peek_at(1) == b'/' {
                        self.advance();
                        self.advance();
                        break;
                    }
                    self.advance();
                }
                continue;
            }
            break;
        }
    }

    fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_whitespace_and_comments();

        if self.at_end() {
            return Ok(Token::eof(self.line, self.col));
        }

        let line = self.line;
        let col = self.col;
        let ch = self.peek();

        // String literals
        if ch == b'"' {
            return self.lex_string(line, col);
        }
        if ch == b'`' {
            return self.lex_raw_string(line, col);
        }

        // Numbers: starts with digit, or '.' followed by digit
        if ch.is_ascii_digit() {
            return self.lex_number(line, col);
        }

        // Identifiers and keywords
        if ch == b'_' || ch.is_ascii_alphabetic() {
            return Ok(self.lex_ident(line, col));
        }

        // Multi-char operators (order matters for longest match)
        self.lex_operator(line, col)
    }

    fn lex_string(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
        self.advance(); // skip opening "
        let start = self.pos;
        while !self.at_end() && self.peek() != b'"' {
            if self.peek() == b'\\' {
                self.advance(); // skip escape char
                if !self.at_end() {
                    self.advance();
                }
            } else {
                self.advance();
            }
        }
        if self.at_end() {
            return Err(LexError {
                line,
                col,
                msg: "unterminated string literal".into(),
            });
        }
        let text = String::from_utf8_lossy(&self.src[start..self.pos]).to_string();
        self.advance(); // skip closing "
        Ok(Token {
            kind: TokenKind::StringLit,
            text,
            line,
            col,
        })
    }

    fn lex_raw_string(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
        self.advance(); // skip opening `
        let start = self.pos;
        while !self.at_end() && self.peek() != b'`' {
            self.advance();
        }
        if self.at_end() {
            return Err(LexError {
                line,
                col,
                msg: "unterminated raw string literal".into(),
            });
        }
        let text = String::from_utf8_lossy(&self.src[start..self.pos]).to_string();
        self.advance(); // skip closing `
        Ok(Token {
            kind: TokenKind::StringLit,
            text,
            line,
            col,
        })
    }

    fn lex_number(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
        let start = self.pos;
        let mut is_float = false;

        // Check for hex/octal prefix
        if self.peek() == b'0' && !self.at_end() {
            let next = self.peek_at(1);
            if next == b'x' || next == b'X' {
                // Hex literal
                self.advance();
                self.advance();
                while !self.at_end() && self.peek().is_ascii_hexdigit() {
                    self.advance();
                }
                let text = String::from_utf8_lossy(&self.src[start..self.pos]).to_string();
                return Ok(Token {
                    kind: TokenKind::IntLit,
                    text,
                    line,
                    col,
                });
            }
        }

        // Consume digits
        while !self.at_end() && self.peek().is_ascii_digit() {
            self.advance();
        }

        // Check for decimal point
        if !self.at_end() && self.peek() == b'.' && self.peek_at(1).is_ascii_digit() {
            is_float = true;
            self.advance(); // skip .
            while !self.at_end() && self.peek().is_ascii_digit() {
                self.advance();
            }
        }

        // Check for exponent
        if !self.at_end() && matches!(self.peek(), b'e' | b'E') {
            is_float = true;
            self.advance();
            if !self.at_end() && matches!(self.peek(), b'+' | b'-') {
                self.advance();
            }
            while !self.at_end() && self.peek().is_ascii_digit() {
                self.advance();
            }
        }

        let text = String::from_utf8_lossy(&self.src[start..self.pos]).to_string();
        Ok(Token {
            kind: if is_float {
                TokenKind::FloatLit
            } else {
                TokenKind::IntLit
            },
            text,
            line,
            col,
        })
    }

    fn lex_ident(&mut self, line: usize, col: usize) -> Token {
        let start = self.pos;
        while !self.at_end() && (self.peek() == b'_' || self.peek().is_ascii_alphanumeric()) {
            self.advance();
        }

        // Check for "eventually-always" (keyword with hyphen)
        if &self.src[start..self.pos] == b"eventually" && self.peek() == b'-' {
            let saved_pos = self.pos;
            let saved_line = self.line;
            let saved_col = self.col;
            self.advance(); // skip -
            let start2 = self.pos;
            while !self.at_end() && (self.peek() == b'_' || self.peek().is_ascii_alphanumeric()) {
                self.advance();
            }
            if &self.src[start2..self.pos] == b"always" {
                return Token {
                    kind: TokenKind::EventuallyAlways,
                    text: "eventually-always".into(),
                    line,
                    col,
                };
            }
            // Not "eventually-always", backtrack
            self.pos = saved_pos;
            self.line = saved_line;
            self.col = saved_col;
        }

        let text = String::from_utf8_lossy(&self.src[start..self.pos]).to_string();
        let kind = keyword_kind(&text).unwrap_or(TokenKind::Ident);
        Token {
            kind,
            text,
            line,
            col,
        }
    }

    fn lex_operator(&mut self, line: usize, col: usize) -> Result<Token, LexError> {
        let ch = self.advance();
        let next = self.peek();

        let (kind, text) = match ch {
            b';' => (TokenKind::Semi, ";"),
            b':' => (TokenKind::Colon, ":"),
            b',' => (TokenKind::Comma, ","),
            b'.' => (TokenKind::Dot, "."),
            b'(' => (TokenKind::LParen, "("),
            b')' => (TokenKind::RParen, ")"),
            b'{' => (TokenKind::LBrace, "{"),
            b'}' => (TokenKind::RBrace, "}"),
            b'[' => (TokenKind::LBracket, "["),
            b']' => (TokenKind::RBracket, "]"),
            b'+' => {
                if next == b'+' {
                    self.advance();
                    (TokenKind::PlusPlus, "++")
                } else {
                    (TokenKind::Plus, "+")
                }
            }
            b'-' => {
                if next == b'>' {
                    self.advance();
                    (TokenKind::Arrow, "->")
                } else if next == b'-' {
                    self.advance();
                    (TokenKind::MinusMinus, "--")
                } else {
                    (TokenKind::Minus, "-")
                }
            }
            b'*' => {
                if next == b'*' {
                    self.advance();
                    (TokenKind::Expo, "**")
                } else {
                    (TokenKind::Star, "*")
                }
            }
            b'/' => (TokenKind::Slash, "/"),
            b'%' => (TokenKind::Percent, "%"),
            b'^' => (TokenKind::Caret, "^"),
            b'&' => {
                if next == b'&' {
                    self.advance();
                    (TokenKind::And, "&&")
                } else if next == b'^' {
                    self.advance();
                    (TokenKind::BitClear, "&^")
                } else {
                    (TokenKind::Amp, "&")
                }
            }
            b'|' => {
                if next == b'|' {
                    self.advance();
                    (TokenKind::Or, "||")
                } else {
                    (TokenKind::Pipe, "|")
                }
            }
            b'!' => {
                if next == b'=' {
                    self.advance();
                    (TokenKind::Neq, "!=")
                } else {
                    (TokenKind::Bang, "!")
                }
            }
            b'=' => {
                if next == b'=' {
                    self.advance();
                    (TokenKind::Eq, "==")
                } else {
                    (TokenKind::Assign, "=")
                }
            }
            b'<' => {
                if next == b'=' {
                    self.advance();
                    (TokenKind::Le, "<=")
                } else if next == b'<' {
                    self.advance();
                    (TokenKind::Lshift, "<<")
                } else if next == b'-' {
                    self.advance();
                    (TokenKind::BackArrow, "<-")
                } else {
                    (TokenKind::Lt, "<")
                }
            }
            b'>' => {
                if next == b'=' {
                    self.advance();
                    (TokenKind::Ge, ">=")
                } else if next == b'>' {
                    self.advance();
                    (TokenKind::Rshift, ">>")
                } else {
                    (TokenKind::Gt, ">")
                }
            }
            _ => {
                return Err(LexError {
                    line,
                    col,
                    msg: format!("unexpected character: '{}'", ch as char),
                });
            }
        };

        Ok(Token {
            kind,
            text: text.into(),
            line,
            col,
        })
    }
}

fn keyword_kind(word: &str) -> Option<TokenKind> {
    Some(match word {
        "spec" => TokenKind::Spec,
        "system" => TokenKind::System,
        "def" => TokenKind::Def,
        "const" => TokenKind::Const,
        "import" => TokenKind::Import,
        "stock" => TokenKind::Stock,
        "flow" => TokenKind::Flow,
        "func" => TokenKind::Func,
        "for" => TokenKind::For,
        "init" => TokenKind::Init,
        "run" => TokenKind::Run,
        "new" => TokenKind::New,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "assert" => TokenKind::Assert,
        "assume" => TokenKind::Assume,
        "when" => TokenKind::When,
        "then" => TokenKind::Then,
        "component" => TokenKind::Component,
        "start" => TokenKind::Start,
        "states" => TokenKind::States,
        "global" => TokenKind::Global,
        "advance" => TokenKind::Advance,
        "stay" => TokenKind::Stay,
        "leave" => TokenKind::Leave,
        "choose" => TokenKind::Choose,
        "this" => TokenKind::This,
        "now" => TokenKind::Now,
        "return" => TokenKind::Return,
        "eventually" => TokenKind::Eventually,
        "always" => TokenKind::Always,
        "nmt" => TokenKind::Nmt,
        "nft" => TokenKind::Nft,
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "nil" => TokenKind::Nil,
        "string" => TokenKind::TyString,
        "bool" => TokenKind::TyBool,
        "int" => TokenKind::TyInt,
        "float" => TokenKind::TyFloat,
        "natural" => TokenKind::TyNatural,
        "uncertain" => TokenKind::TyUncertain,
        "unknown" => TokenKind::TyUnknown,
        _ => return None,
    })
}

#[derive(Debug, Clone)]
pub struct LexError {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.msg)
    }
}

impl std::error::Error for LexError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        Lexer::new(src)
            .tokenize()
            .unwrap()
            .into_iter()
            .map(|t| t.kind)
            .collect()
    }

    #[test]
    fn spec_decl() {
        assert_eq!(
            kinds("spec simple;"),
            vec![
                TokenKind::Spec,
                TokenKind::Ident,
                TokenKind::Semi,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn flow_operators() {
        assert_eq!(
            kinds("x <- 5; y -> 3; z = 1;"),
            vec![
                TokenKind::Ident,
                TokenKind::BackArrow,
                TokenKind::IntLit,
                TokenKind::Semi,
                TokenKind::Ident,
                TokenKind::Arrow,
                TokenKind::IntLit,
                TokenKind::Semi,
                TokenKind::Ident,
                TokenKind::Assign,
                TokenKind::IntLit,
                TokenKind::Semi,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn comparison_ops() {
        assert_eq!(
            kinds("a == b != c < d <= e > f >= g"),
            vec![
                TokenKind::Ident,
                TokenKind::Eq,
                TokenKind::Ident,
                TokenKind::Neq,
                TokenKind::Ident,
                TokenKind::Lt,
                TokenKind::Ident,
                TokenKind::Le,
                TokenKind::Ident,
                TokenKind::Gt,
                TokenKind::Ident,
                TokenKind::Ge,
                TokenKind::Ident,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn string_literal() {
        let toks = Lexer::new(r#""hello world""#).tokenize().unwrap();
        assert_eq!(toks[0].kind, TokenKind::StringLit);
        assert_eq!(toks[0].text, "hello world");
    }

    #[test]
    fn float_literal() {
        let toks = Lexer::new("3.14 1e10 2.5e-3").tokenize().unwrap();
        assert_eq!(toks[0].kind, TokenKind::FloatLit);
        assert_eq!(toks[0].text, "3.14");
        assert_eq!(toks[1].kind, TokenKind::FloatLit);
        assert_eq!(toks[2].kind, TokenKind::FloatLit);
    }

    #[test]
    fn eventually_always_keyword() {
        let toks = Lexer::new("eventually-always eventually")
            .tokenize()
            .unwrap();
        assert_eq!(toks[0].kind, TokenKind::EventuallyAlways);
        assert_eq!(toks[1].kind, TokenKind::Eventually);
    }

    #[test]
    fn comments_skipped() {
        let toks = Lexer::new("x // comment\ny /* block */ z")
            .tokenize()
            .unwrap();
        let ks: Vec<_> = toks.iter().map(|t| t.kind).collect();
        assert_eq!(
            ks,
            vec![
                TokenKind::Ident,
                TokenKind::Ident,
                TokenKind::Ident,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn all_keywords() {
        let src = "spec system def const import stock flow func for init run new if else \
                   assert assume when then component start states global advance stay leave \
                   choose this now return eventually always nmt nft true false nil \
                   string bool int float natural uncertain unknown";
        let toks = Lexer::new(src).tokenize().unwrap();
        // All tokens except Eof should be keyword kinds (not Ident)
        for tok in &toks[..toks.len() - 1] {
            assert_ne!(
                tok.kind,
                TokenKind::Ident,
                "expected keyword, got ident: {}",
                tok.text
            );
        }
    }

    #[test]
    fn expo_vs_star() {
        assert_eq!(
            kinds("a ** b * c"),
            vec![
                TokenKind::Ident,
                TokenKind::Expo,
                TokenKind::Ident,
                TokenKind::Star,
                TokenKind::Ident,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn pipe_vs_or() {
        assert_eq!(
            kinds("a | b || c"),
            vec![
                TokenKind::Ident,
                TokenKind::Pipe,
                TokenKind::Ident,
                TokenKind::Or,
                TokenKind::Ident,
                TokenKind::Eof,
            ]
        );
    }
}
