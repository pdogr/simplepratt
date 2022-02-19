use thiserror::Error;

use crate::lexer::Token;

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("expected token")]
    MissingToken,

    #[error("unexpected token {token:?}")]
    UnexpectedToken { token: Token },

    #[error("expected token: {expected:?}; actual token: {actual:?}")]
    TokenMismatch { expected: Token, actual: Token },

    #[error("expected token: {expected:?}; found no token")]
    MissingExpectedToken { expected: Token },
}
