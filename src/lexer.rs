use logos::{Lexer, Logos};
use std::fmt::Display;

use crate::PrattOperator;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum OpType {
    Add,
    Sub,
    Mul,
    Div,
    Assign,
    Power,
    Fact,
}

impl Display for OpType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpType::Add => write!(f, "+"),
            OpType::Sub => write!(f, "-"),
            OpType::Mul => write!(f, "*"),
            OpType::Div => write!(f, "/"),
            OpType::Assign => write!(f, "="),
            OpType::Power => write!(f, "^"),
            OpType::Fact => write!(f, "!"),
        }
    }
}

fn op(lex: &mut Lexer<Token>) -> Option<OpType> {
    let slice = lex.slice();
    let mut chars = slice.chars();
    let op = if let Some(ch) = chars.next() {
        match ch {
            '+' => OpType::Add,
            '-' => OpType::Sub,
            '*' => OpType::Mul,
            '/' => OpType::Div,
            '=' => OpType::Assign,
            '^' => OpType::Power,
            '!' => OpType::Fact,
            _ => return None,
        }
    } else {
        return None;
    };
    Some(op)
}

impl PrattOperator for Token {
    fn lbp(&self) -> usize {
        match self {
            Token::Op(op) => match op {
                OpType::Assign => 10,
                OpType::Add | OpType::Sub => 20,
                OpType::Mul | OpType::Div => 30,
                OpType::Power => 50,
                OpType::Fact => 40,
            },
            Token::LeftSquare => 60,
            Token::Question => 15,
            Token::Dot => 70,
            _ => usize::MIN,
        }
    }

    fn rbp(&self) -> usize {
        match self {
            Token::Op(op) => {
                match op {
                    OpType::Assign => self.lbp(),

                    // Add, Sub, Mul, Div are left associative
                    OpType::Add | OpType::Sub | OpType::Mul | OpType::Div => self.lbp() + 1,

                    // Power is right associative
                    OpType::Power => self.lbp(),

                    // usize::MIN denotes that this op cannot have a right operand
                    OpType::Fact => usize::MIN,
                }
            }
            Token::LeftSquare => self.lbp() + 1,
            Token::Question | Token::Dot => self.lbp(),

            // usize::MIN denotes that this op cannot have a right operand
            _ => usize::MIN,
        }
    }

    fn nbp(&self) -> usize {
        match self {
            Token::Op(op) => {
                match op {
                    // Assign is non associative
                    OpType::Assign => self.lbp() - 1,

                    // Factorial is a postfix so any operator can come to its right
                    // eg. a! ^ b
                    OpType::Fact => usize::MAX,
                    _ => return self.lbp(),
                }
            }
            _ => return self.lbp(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Logos)]
pub enum Token {
    #[token("(")]
    LeftParen,

    #[token(")")]
    RightParen,

    #[token("[")]
    LeftSquare,

    #[token("]")]
    RightSquare,

    #[token(":")]
    Colon,

    #[token("?")]
    Question,

    #[token("if")]
    If,

    #[token("then")]
    Then,

    #[token("else")]
    Else,

    #[token(".")]
    Dot,

    #[regex("[a-zA-Z]+", |s| s.slice().to_string())]
    Text(String),

    #[regex("[0-9]+", |s| s.slice().parse())]
    Int(i64),

    #[regex(r"[+\-\*/=\^!]", op)]
    Op(OpType),

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}

#[test]
fn simple_text() {
    let mut lex = Token::lexer("asdasda");
    assert_eq!(lex.next(), Some(Token::Text("asdasda".into())));
    assert_eq!(lex.next(), None);
}

#[test]
fn operators() {
    let lex = Token::lexer("+ - * / ^ ! =");
    let tokens: Vec<_> = lex.into_iter().collect();
    assert_eq!(
        tokens,
        &[
            Token::Op(OpType::Add),
            Token::Op(OpType::Sub),
            Token::Op(OpType::Mul),
            Token::Op(OpType::Div),
            Token::Op(OpType::Power),
            Token::Op(OpType::Fact),
            Token::Op(OpType::Assign)
        ]
    )
}

#[test]
fn num() {
    let lex = Token::lexer("(1 + 2)");
    let tokens: Vec<_> = lex.into_iter().collect();
    assert_eq!(
        tokens,
        &[
            Token::LeftParen,
            Token::Int(1),
            Token::Op(OpType::Add),
            Token::Int(2),
            Token::RightParen
        ]
    );
}
