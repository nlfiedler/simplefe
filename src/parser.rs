//
// Copyright 2022 Nathan Fiedler
//
use crate::lexer::{lex, TokenType};
use anyhow::{anyhow, Error};

///
/// Result of parsing textual input into an expression that consists of an
/// "statement" and zero or more "arguments".
///
#[derive(Debug)]
pub struct Expression {
    pub statement: String,
    pub arguments: Vec<String>,
}

/// Parse the text into an expression.
pub fn parse(input: &str) -> Result<Expression, Error> {
    let rx = lex(input);
    let statement = if let Ok(token) = rx.recv() {
        if token.typ == TokenType::Identifier {
            token.val
        } else {
            return Err(anyhow!("expected identifier, got {}", token.val));
        }
    } else {
        return Err(anyhow!("missing statement"));
    };
    let mut arguments: Vec<String> = Vec::new();
    if let Ok(token) = rx.recv() {
        if token.typ == TokenType::OpenParen {
            while let Ok(token) = rx.recv() {
                if token.typ == TokenType::Identifier {
                    arguments.push(token.val);
                } else if token.typ == TokenType::CloseParen {
                    break;
                } else if token.typ == TokenType::EndOfFile {
                    return Err(anyhow!("expected ')'"));
                } else if token.typ != TokenType::Comma {
                    return Err(anyhow!("unexpected token: {}", token.val));
                }
            }
        } else if token.typ != TokenType::EndOfFile {
            return Err(anyhow!("expected '(' got {}", token.val));
        }
    }
    Ok(Expression {
        statement,
        arguments,
    })
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn test_parse_empty_string() {
        let result = parse("");
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("expected identifier"));
    }

    #[test]
    fn test_parse_missing_close_paren() {
        let result = parse("are_friends(nako, bocchi");
        println!("reslt: {:?}", result);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "expected ')'");
    }

    #[test]
    fn test_parse_missing_open_paren() {
        let result = parse("are_friends nako, bocchi");
        println!("reslt: {:?}", result);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "expected '(' got nako");
    }

    #[test]
    fn test_parse_unexpected_token() {
        let result = parse("are_friends(nako (bocchi");
        println!("reslt: {:?}", result);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "unexpected token: (");
    }

    #[test]
    fn test_parse_trailing_comma() {
        // trailing comma but missing close paren
        let result = parse("are_friends(nako,");
        println!("reslt: {:?}", result);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "expected ')'");

        // trailing comma is otherwise okay
        let result = parse("has_friends(bocchi,)");
        assert!(result.is_ok());
        let expr = result.unwrap();
        assert_eq!(expr.statement, "has_friends");
        assert_eq!(expr.arguments.len(), 1);
        assert_eq!(expr.arguments[0], "bocchi");
    }

    #[test]
    fn test_parse_lonely_statement() {
        let result = parse("has_friends");
        assert!(result.is_ok());
        let expr = result.unwrap();
        assert_eq!(expr.statement, "has_friends");
        assert_eq!(expr.arguments.len(), 0);
    }

    #[test]
    fn test_parse_one_argument() {
        let result = parse("has_friends ( bocchi )");
        assert!(result.is_ok());
        let expr = result.unwrap();
        assert_eq!(expr.statement, "has_friends");
        assert_eq!(expr.arguments.len(), 1);
        assert_eq!(expr.arguments[0], "bocchi");
    }

    #[test]
    fn test_parse_two_arguments() {
        let result = parse("are_friends(nako,bocchi)");
        assert!(result.is_ok());
        let expr = result.unwrap();
        assert_eq!(expr.statement, "are_friends");
        assert_eq!(expr.arguments.len(), 2);
        assert_eq!(expr.arguments[0], "nako");
        assert_eq!(expr.arguments[1], "bocchi");
    }

    #[test]
    fn test_parse_three_arguments() {
        let result = parse("triple(3, 4, 5)");
        assert!(result.is_ok());
        let expr = result.unwrap();
        assert_eq!(expr.statement, "triple");
        assert_eq!(expr.arguments.len(), 3);
        assert_eq!(expr.arguments[0], "3");
        assert_eq!(expr.arguments[1], "4");
        assert_eq!(expr.arguments[2], "5");
    }
}
