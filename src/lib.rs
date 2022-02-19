#![allow(dead_code)]
mod ast;

mod error;

mod lexer;

mod parser;

pub type Result<R> = std::result::Result<R, error::ParseError>;

trait PrattOperator {
    // LBP "left binding power"
    // None denotes that this operator cannot have an operand to its left
    fn lbp(&self) -> usize;

    // RBP "right binding power"
    // Bonding power of this operator to its right operand
    // If left associative RBP > LBP
    // If right associative RBP <= LBP
    fn rbp(&self) -> usize;

    // NBP "next binding power"
    // Highest power of the operator that this operator can be a left of
    // Default is LBP as we expect this operator to be associative with itself atleast
    // If not associative then NBP < LBP, override this fn
    fn nbp(&self) -> usize {
        self.lbp()
    }
}
