use std::fmt::Display;

use crate::lexer::OpType;

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Ident(String),
    Int(i64),
    PrefixExpr(OpType, Box<Expr>),
    PostfixExpr(OpType, Box<Expr>),
    BinaryExpr(OpType, Box<Expr>, Box<Expr>),
    TernaryExpr(Box<Expr>, Box<Expr>, Box<Expr>),
    IndexedExpr(Box<Expr>, Box<Expr>),
    CondExpr(Box<Expr>, Box<Expr>, Box<Expr>),
    CompositionExpr(Box<Expr>, Box<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Ident(i) => write!(f, "{}", i),
            Expr::Int(i) => write!(f, "{}", i),
            Expr::BinaryExpr(op, e1, e2) => write!(f, "({} {} {})", op, e1, e2),
            Expr::PostfixExpr(op, e) => write!(f, "({} {})", op, e),
            Expr::PrefixExpr(op, e) => write!(f, "({} {})", op, e),
            Expr::IndexedExpr(e1, e2) => write!(f, "([] {} {})", e1, e2),
            Expr::CondExpr(cond, if_true, if_false) => {
                write!(f, "(if {} then {} else {})", cond, if_true, if_false)
            }
            Expr::CompositionExpr(e1, e2) => write!(f, "(. {} {})", e1, e2),
            Expr::TernaryExpr(cond, if_true, if_false) => {
                write!(f, "(? {} {} {})", cond, if_true, if_false)
            }
        }
    }
}
