//
// Copyright 2022 Nathan Fiedler
//
use std::fmt;
use std::str::CharIndices;
use std::sync::mpsc::{self, Receiver, SyncSender};
use std::thread;

/// Defines the type of a particular token.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TokenType {
    Error,
    OpenParen,
    CloseParen,
    Comma,
    Identifier,
    EndOfFile,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenType::Error => write!(f, "Error"),
            TokenType::OpenParen => write!(f, "OpenParen"),
            TokenType::CloseParen => write!(f, "CloseParen"),
            TokenType::Comma => write!(f, "Comma"),
            TokenType::Identifier => write!(f, "Identifier"),
            TokenType::EndOfFile => write!(f, "EOF"),
        }
    }
}

/// Represents a single token emitted by the lexer.
#[derive(PartialEq, Debug)]
pub struct Token {
    /// The type of the token.
    pub typ: TokenType,
    /// Text of the token, typically taken directly from the input.
    pub val: String,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Token[{}: '{}']", self.typ, self.val)
    }
}

/// The `Lexer` struct holds the state of the lexical analyzer.
pub struct Lexer<'a> {
    // the string being scanned
    input: &'a str,
    // iterator of the characters in the string
    iter: CharIndices<'a>,
    // the next character to return, if peek() has been called
    peeked: Option<(usize, char)>,
    // start position of the current token (in bytes)
    start: usize,
    // position of next character to read (in bytes)
    pos: usize,
    // width of last character read from input (in bytes)
    width: usize,
    // channel sender for scanned tokens
    chan: SyncSender<Token>,
}

impl<'a> Lexer<'a> {
    /// `new` constructs an instance of `Lexer` for the named input.
    fn new(input: &'a str, chan: SyncSender<Token>) -> Lexer<'a> {
        Lexer {
            input,
            iter: input.char_indices(),
            peeked: None,
            start: 0,
            pos: 0,
            width: 0,
            chan,
        }
    }

    /// emit passes the current token back to the client via the channel.
    fn emit(&mut self, t: TokenType) {
        let text = &self.input[self.start..self.pos];
        let _ = self.chan.send(Token {
            typ: t,
            val: text.to_string(),
        });
        self.start = self.pos;
    }

    /// emit_text passes the given token back to the client via the channel.
    fn emit_text(&mut self, t: TokenType, text: &str) {
        let _ = self.chan.send(Token {
            typ: t,
            val: text.to_string(),
        });
        self.start = self.pos;
    }

    /// `next` returns the next rune in the input, or `None` if at the end.
    fn next(&mut self) -> Option<char> {
        let next = if self.peeked.is_some() {
            self.peeked.take()
        } else {
            self.iter.next()
        };
        match next {
            Some((pos, ch)) => {
                self.width = ch.len_utf8();
                self.pos = pos + self.width;
                Some(ch)
            }
            None => None,
        }
    }

    /// `peek` returns but does not consume the next rune in the input.
    fn peek(&mut self) -> Option<char> {
        if self.peeked.is_none() {
            self.peeked = self.iter.next();
        }
        match self.peeked {
            Some((_, ch)) => Some(ch),
            None => None,
        }
    }

    /// `ignore` skips over the pending input before this point.
    fn ignore(&mut self) {
        self.start = self.pos;
    }

    /// `accept_run` consumes a run of runes from the valid set.
    fn accept_run(&mut self, valid: &str) -> bool {
        let old_pos = self.pos;
        while let Some(ch) = self.peek() {
            if valid.contains(ch) {
                // consume the character
                self.next();
            } else {
                break;
            }
        }
        old_pos < self.pos
    }
}

struct StateFn(fn(&mut Lexer) -> Option<StateFn>);

/// Runs the lexical analysis on the text and returns the results.
pub fn lex(input: &str) -> Receiver<Token> {
    let sanitized = sanitize_input(input);
    let (tx, rx) = mpsc::sync_channel(1);
    thread::spawn(move || {
        let mut lexer = Lexer::new(&*sanitized, tx);
        // inform the compiler what the type of state _really_ is
        let mut state: fn(&mut Lexer) -> Option<StateFn> = lex_start;
        while let Some(next) = state(&mut lexer) {
            let StateFn(state_fn) = next;
            state = state_fn;
        }
    });
    rx
}

/// `errorf` emits an error token and returns `None` to end lexing.
fn errorf(l: &mut Lexer, message: &str) -> Option<StateFn> {
    l.emit_text(TokenType::Error, message);
    None
}

/// `sanitize_input` prepares the input program for lexing, which basically
/// means converting various end-of-line character sequences to a single
/// form, namely newlines.
fn sanitize_input(input: &str) -> String {
    input.replace("\r\n", "\n").replace("\r", "\n")
}

fn lex_start(l: &mut Lexer) -> Option<StateFn> {
    if let Some(ch) = l.next() {
        if ch == '(' {
            l.emit(TokenType::OpenParen);
            Some(StateFn(lex_start))
        } else if ch == ')' {
            l.emit(TokenType::CloseParen);
            Some(StateFn(lex_start))
        } else if ch == ',' {
            l.emit(TokenType::Comma);
            Some(StateFn(lex_start))
        } else if ch.is_alphanumeric() {
            Some(StateFn(lex_identifier))
        } else if ch.is_whitespace() {
            Some(StateFn(lex_separator))
        } else {
            let msg = format!("unknown character: {}", ch);
            return errorf(l, &msg);
        }
    } else {
        l.emit(TokenType::EndOfFile);
        None
    }
}

/// `lex_separator` expects the current position to be the start of a
/// separator and advances until it finds the end of that separator.
/// No token will be emitted since separators are ignored.
fn lex_separator(l: &mut Lexer) -> Option<StateFn> {
    l.accept_run(" \t\n\r");
    l.ignore();
    Some(StateFn(lex_start))
}

/// `lex_identifier` processes the text as an identifier.
fn lex_identifier(l: &mut Lexer) -> Option<StateFn> {
    while let Some(ch) = l.peek() {
        if ch.is_alphanumeric() || ch == '_' {
            l.next();
        } else if is_delimiter(ch) {
            break;
        } else {
            return errorf(l, "improperly terminated identifier");
        }
    }
    l.emit(TokenType::Identifier);
    Some(StateFn(lex_start))
}

/// `is_delimiter` returns true if `ch` is a delimiter character.
fn is_delimiter(ch: char) -> bool {
    match ch {
        ' ' | '.' | ',' | ';' | '(' | ')' | '"' => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// `verify_success` lexes a program and verifies that the tokens
    /// emitted match those in the vector of tuples.
    fn verify_success(input: &str, expected: Vec<(TokenType, &str)>) {
        let rx = lex(input);
        for er in expected.iter() {
            if let Ok(token) = rx.recv() {
                assert_eq!(token.typ, er.0);
                assert_eq!(token.val, er.1);
            } else {
                assert!(false, "ran out of tokens");
            }
        }
        // make sure we have reached the end of the results
        if let Ok(token) = rx.recv() {
            assert_eq!(token.typ, TokenType::EndOfFile);
        } else {
            assert!(false, "should have exhausted tokens");
        }
    }

    /// `verify_errors` checks that the input (map key) produces an error
    /// containing the substring given as the map value.
    fn verify_errors(inputs: HashMap<&str, &str>) {
        for (input, expected) in inputs.iter() {
            let rx = lex(input);
            if let Ok(token) = rx.recv() {
                assert_eq!(token.typ, TokenType::Error);
                assert!(token.val.contains(expected), "expected {} error", expected);
            } else {
                assert!(false, "ran out of tokens");
            }
        }
    }

    #[test]
    fn test_open_close_paren() {
        let mut vec = Vec::new();
        vec.push((TokenType::OpenParen, "("));
        vec.push((TokenType::CloseParen, ")"));
        verify_success("()", vec);
    }

    #[test]
    fn test_simple_expression() {
        let mut vec = Vec::new();
        vec.push((TokenType::Identifier, "has_friends"));
        vec.push((TokenType::OpenParen, "("));
        vec.push((TokenType::Identifier, "bocchi"));
        vec.push((TokenType::CloseParen, ")"));
        verify_success("has_friends(bocchi)", vec);
    }

    #[test]
    fn test_variable_arguments() {
        let mut vec = Vec::new();
        vec.push((TokenType::Identifier, "has_friends"));
        vec.push((TokenType::OpenParen, "("));
        vec.push((TokenType::Identifier, "X"));
        vec.push((TokenType::CloseParen, ")"));
        verify_success("has_friends (X)", vec);
    }

    #[test]
    fn test_numeric_arguments() {
        let mut vec = Vec::new();
        vec.push((TokenType::Identifier, "three_tuple"));
        vec.push((TokenType::OpenParen, "("));
        vec.push((TokenType::Identifier, "3"));
        vec.push((TokenType::Comma, ","));
        vec.push((TokenType::Identifier, "4"));
        vec.push((TokenType::Comma, ","));
        vec.push((TokenType::Identifier, "5"));
        vec.push((TokenType::CloseParen, ")"));
        verify_success("three_tuple (3, 4, 5)", vec);
    }

    #[test]
    fn test_ignore_whitespace() {
        let mut vec = Vec::new();
        vec.push((TokenType::Identifier, "are_friends"));
        vec.push((TokenType::OpenParen, "("));
        vec.push((TokenType::Identifier, "nako"));
        vec.push((TokenType::Comma, ","));
        vec.push((TokenType::Identifier, "bocchi"));
        vec.push((TokenType::CloseParen, ")"));
        verify_success(" are_friends ( nako , bocchi ) ", vec);
    }

    #[test]
    fn test_error_cases() {
        let mut map = HashMap::new();
        map.insert("abc]", "improperly terminated identifier");
        map.insert(";", "unknown character: ;");
        verify_errors(map);
    }
}
