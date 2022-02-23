use std::iter::Peekable;

use logos::Logos;

use crate::ast::*;
use crate::error::ParseError;
use crate::lexer::*;
use crate::PrattOperator;
use crate::Result;

// Grammar
// E -> P | E + E | E - E | E * E | E / E
// P -> Int | Ident
struct Parser<I: Iterator<Item = Token>> {
    stream: Peekable<I>,
}

impl<I: Iterator<Item = Token>> Parser<I> {
    pub fn new(stream: I) -> Self {
        Self {
            stream: stream.peekable(),
        }
    }

    fn next(&mut self) -> Result<Token> {
        match self.stream.next() {
            Some(t) => Ok(t),
            None => Err(ParseError::MissingToken),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<()> {
        match self.stream.peek() {
            Some(actual) if *actual == expected => {
                self.stream.next();
                Ok(())
            }
            Some(actual) => Err(ParseError::TokenMismatch {
                expected,
                actual: actual.clone(),
            }),
            None => Err(ParseError::MissingExpectedToken { expected }),
        }
    }

    pub fn parse(&mut self) -> Result<Expr> {
        self.parse_e(1)
    }

    fn parse_e(&mut self, min_bp: usize) -> Result<Expr> {
        // This is the max binding power which is allowed for an operator
        let mut max_bp: usize = usize::MAX;

        // Ast is the ast generated till now in parsing the Expr E
        // E has to start with P so we initalize E with P
        let mut ast = self.parse_p()?;
        loop {
            // If there is no next token in stream we are done hence break
            let tok = match self.stream.peek() {
                Some(t) => t,
                None => break,
            };

            // Get LBP, RBP for the operator
            let (lbp, rbp) = (tok.lbp(), tok.rbp());

            // If min_bp <= lbp <= max_bp we continue else break
            if lbp < min_bp || lbp > max_bp {
                break;
            }

            // We know if we have reached here
            // the next token is an operator so we extract it
            let tok = self.stream.next().unwrap();

            match tok {
                Token::Op(op) => match op {
                    OpType::Add
                    | OpType::Sub
                    | OpType::Mul
                    | OpType::Div
                    | OpType::Assign
                    | OpType::Power => {
                        // Parse the remaining expr with new current binding power as RBP
                        let inner_ast = self.parse_e(rbp)?;

                        // Update ast
                        ast = Expr::BinaryExpr(op, Box::new(ast), Box::new(inner_ast));
                    }
                    OpType::Fact => {
                        ast = Expr::PostfixExpr(op, Box::new(ast));
                    }
                },
                Token::LeftSquare => {
                    // Parse the inner which is the index amount
                    let inner_ast = self.parse_e(1)?;

                    // We expect ']' after index operation
                    self.expect(Token::RightSquare)?;

                    // Return new indexed expression
                    ast = Expr::IndexedExpr(Box::new(ast), Box::new(inner_ast));
                }
                Token::Question => {
                    // Next must be the condition expression
                    let if_true = self.parse_e(1)?;

                    // Each if must be matched with else
                    self.expect(Token::Colon)?;
                    // Parse false expression
                    let if_false = self.parse_e(rbp)?;

                    ast = Expr::TernaryExpr(Box::new(ast), Box::new(if_true), Box::new(if_false));
                }
                Token::Dot => {
                    // Parse the remaining expr with new current binding power as RBP
                    let inner_ast = self.parse_e(rbp)?;

                    // Update ast
                    ast = Expr::CompositionExpr(Box::new(ast), Box::new(inner_ast));
                }
                _ => unreachable!(),
            }
            max_bp = tok.nbp();
        }
        Ok(ast)
    }
    // N-type tokens (which can start an expression)
    fn parse_p(&mut self) -> Result<Expr> {
        let next = self.next()?;
        let ast = match next {
            Token::Text(t) => Expr::Ident(t),
            Token::Int(i) => Expr::Int(i),
            Token::LeftParen => {
                let ast = self.parse_e(1)?;
                let () = self.expect(Token::RightParen)?;
                return Ok(ast);
            }

            // Prefix operator '-'
            Token::Op(op) if op == OpType::Sub => {
                let rbp = next.rbp();
                let mut ast = self.parse_e(rbp)?;
                ast = Expr::PrefixExpr(op, Box::new(ast));
                return Ok(ast);
            }

            // If token
            Token::If => {
                let cond = self.parse_e(1)?;
                self.expect(Token::Then)?;

                let if_true = self.parse_e(1)?;
                self.expect(Token::Else)?;

                let if_false = self.parse_e(1)?;

                let ast = Expr::CondExpr(Box::new(cond), Box::new(if_true), Box::new(if_false));
                return Ok(ast);
            }
            t => return Err(ParseError::UnexpectedToken { token: t }),
        };
        Ok(ast)
    }
}

fn parse(s: &str) -> Expr {
    let lex = Token::lexer(s);
    let mut parser = Parser::new(lex.into_iter());
    parser.parse().expect("parsing error")
}

#[test]
fn atom() {
    let s = parse("1");
    assert_eq!(s.to_string(), "1");

    let s = parse("abcd");
    assert_eq!(s.to_string(), "abcd");
}

#[test]
fn add() {
    let s = parse("a + b + c");
    assert_eq!(s.to_string(), "(+ (+ a b) c)");
}

#[test]
fn power() {
    let s = parse("a ^ b ^ c");
    assert_eq!(s.to_string(), "(^ a (^ b c))");
}

#[test]
fn mix() {
    let s = parse("1 + 2 * 3");
    assert_eq!(s.to_string(), "(+ 1 (* 2 3))");

    let s = parse("a + b * c * d + e");
    assert_eq!(s.to_string(), "(+ (+ a (* (* b c) d)) e)");
}

#[test]
fn assignment() {
    let s = parse("a = 1 + 2 * 3");
    assert_eq!(s.to_string(), "(= a (+ 1 (* 2 3)))");
}

#[test]
fn factorial() {
    let s = parse("a = 1! + 2");
    assert_eq!(s.to_string(), "(= a (+ (! 1) 2))");
}

#[test]
fn pow_mul() {
    let s = parse("a! * b");
    assert_eq!(s.to_string(), "(* (! a) b)");
}

#[test]
fn pow_factorial() {
    let s = parse("a! ^ b");
    assert_eq!(s.to_string(), "(^ (! a) b)");
}

#[test]
fn pow_factorial_mix() {
    let s = parse("a ^ b ! ^ c");
    assert_eq!(s.to_string(), "(^ (! (^ a b)) c)");
}

#[test]
fn bracket_expr() {
    let s = parse("(a+b)");
    assert_eq!(s.to_string(), "(+ a b)");
}

#[test]
fn prefix_sub() {
    let s = parse("-(a+b)");
    assert_eq!(s.to_string(), "(- (+ a b))");
}

#[test]
fn array_index() {
    let s = parse("a[1][2]");
    assert_eq!(s.to_string(), "([] ([] a 1) 2)");
}

#[test]
fn parse_ternary() {
    let s = parse(" a= 1 ? b: 2");
    assert_eq!(s.to_string(), "(= a (? 1 b 2))");
}

#[test]
fn parse_if() {
    let s = parse("if cond then a+1 else -a-2");
    assert_eq!(s.to_string(), "(if cond then (+ a 1) else (- (- a) 2))");
}

// Test from
// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
#[test]
fn tests() {
    let s = parse("1");
    assert_eq!(s.to_string(), "1");

    let s = parse("1 + 2 * 3");
    assert_eq!(s.to_string(), "(+ 1 (* 2 3))");

    let s = parse("a + b * c * d + e");
    assert_eq!(s.to_string(), "(+ (+ a (* (* b c) d)) e)");

    let s = parse("f . g . h");
    assert_eq!(s.to_string(), "(. f (. g h))");

    let s = parse(" 1 + 2 + f . g . h * 3 * 4");
    assert_eq!(s.to_string(), "(+ (+ 1 2) (* (* (. f (. g h)) 3) 4))",);

    /* Disabling as currently I assume Infix binding power is same as LBP
    let s = parse("--1 * 2");
    assert_eq!(s.to_string(), "(* (- (- 1)) 2)");
    */

    let s = parse("--f . g");
    assert_eq!(s.to_string(), "(- (- (. f g)))");

    let s = parse("-9!");
    assert_eq!(s.to_string(), "(- (! 9))");

    let s = parse("f . g !");
    assert_eq!(s.to_string(), "(! (. f g))");

    let s = parse("(((0)))");
    assert_eq!(s.to_string(), "0");

    let s = parse("x[0][1]");
    assert_eq!(s.to_string(), "([] ([] x 0) 1)");

    let s = parse(
        "a ? b :
         c ? d
         : e",
    );
    assert_eq!(s.to_string(), "(? a b (? c d e))");

    let s = parse("a = 0 ? b : c = d");
    assert_eq!(s.to_string(), "(= a (= (? 0 b c) d))");
}
