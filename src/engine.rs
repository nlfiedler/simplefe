//
// Copyright 2022 Nathan Fiedler
//
use anyhow::Error;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter::zip;

/// A symbol in the fact engine.
type Symbol = u32;

///
/// Maps names to distinct symbols.
///
struct SymbolRegistry {
    // mapping of names to values
    values: HashMap<String, Symbol>,
    // mapping of values to names
    names: HashMap<Symbol, String>,
    // monotonically increasing symbol value
    counter: u32,
}

impl SymbolRegistry {
    /// Construct an instance of SymbolRegistry.
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
            names: HashMap::new(),
            counter: 0,
        }
    }

    /// Produce a symbol value for the given name.
    ///
    /// Either returns the previously assigned value or creates a new mapping in
    /// the registry.
    pub fn value(&mut self, name: &str) -> Symbol {
        if let Some(value) = self.values.get(name) {
            *value
        } else {
            self.counter += 1;
            self.values.insert(name.into(), self.counter);
            self.names.insert(self.counter, name.into());
            self.counter
        }
    }

    /// Retrieve the symbol name for a given value.
    pub fn name(&self, value: &Symbol) -> Option<String> {
        self.names.get(value).map(|n| n.to_string())
    }
}

///
/// A fact with its statement and set of arguments.
///
#[derive(Eq, Hash, PartialEq)]
struct Fact {
    statement: Symbol,
    arguments: Vec<Symbol>,
}

impl Fact {
    /// Construct an instance of Fact.
    pub fn new(statement: Symbol, arguments: Vec<Symbol>) -> Self {
        Self {
            statement,
            arguments,
        }
    }

    /// Check if the given query matches this fact.
    ///
    /// Returns `FALSE` if the query does not match, and `TRUE` if it does and
    /// there are no variable arguments. If the query matches and any arguments
    /// are variables, then a mapping of variable names to values is returned.
    pub fn matches(&self, symbols: &SymbolRegistry, query: &Query) -> Response {
        if self.statement == query.statement {
            if self.arguments.len() == query.arguments.len() {
                // single-assignment variables and their bound values
                let mut vars: HashMap<String, Symbol> = HashMap::new();
                // variables and their values in the encountered order
                let mut ordered: Vec<(String, Symbol)> = Vec::new();
                // match each fact's argument with the query's argument
                for (a, q) in zip(self.arguments.iter(), query.arguments.iter()) {
                    match q {
                        QueryArgument::SYMBOL(s) => {
                            // symbols do not match
                            if a != s {
                                return Response::FALSE;
                            }
                        }
                        QueryArgument::VARIABLE(n) => {
                            // Ensure that each variable is assigned one time,
                            // or that the value being assigned matches the one
                            // assigned previously; otherwise this fact does not
                            // match the query.
                            let name = n.to_string();
                            if let Some(v) = vars.get(&name) {
                                if v != a {
                                    return Response::FALSE;
                                }
                            } else {
                                vars.insert(name, *a);
                                ordered.push((n.to_string(), *a));
                            }
                        }
                    }
                }
                if vars.is_empty() {
                    return Response::TRUE;
                } else {
                    // Convert the symbols into their corresponding names. The
                    // unwrap() on the symbol name retrieval should never panic
                    // since the query arguments were registered earlier.
                    let result: Vec<(String, String)> = ordered
                        .into_iter()
                        .map(|(n, v)| (n, symbols.name(&v).unwrap()))
                        .collect();
                    return Response::MAP(result);
                }
            }
        }
        Response::FALSE
    }
}

/// Query arguments can be symbols or variable names.
#[derive(Clone, Eq, Hash, PartialEq)]
enum QueryArgument {
    SYMBOL(Symbol),
    VARIABLE(String),
}

impl QueryArgument {
    /// Create a QueryArgument from the string, which either represents a symbol
    /// (does not start with an uppercase letter) or a variable (starts with an
    /// uppercase letter).
    fn from_str(symbols: &mut SymbolRegistry, name: &str) -> Self {
        // not quite Erlang, but it conforms to the specification
        if let Some(ch) = name.chars().next() {
            if ch.is_uppercase() {
                return QueryArgument::VARIABLE(name.into());
            }
        }
        QueryArgument::SYMBOL(symbols.value(name))
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct Query {
    statement: Symbol,
    arguments: Vec<QueryArgument>,
}

impl Query {
    /// Construct an instance of Query.
    pub fn new(statement: Symbol, arguments: Vec<QueryArgument>) -> Self {
        Self {
            statement,
            arguments,
        }
    }
}

///
/// Response from a query of the fact engine.
///
#[derive(Debug, Eq, PartialEq)]
pub enum Response {
    /// Represents a matching result.
    TRUE,
    /// Represents a non-matching result.
    FALSE,
    /// List of variable names and the matched symbol names.
    MAP(Vec<(String, String)>),
}

impl Response {
    /// Returns true if the response is a map.
    pub fn is_map(&self) -> bool {
        matches!(*self, Response::MAP(_))
    }
}

impl fmt::Display for Response {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Response::TRUE => write!(f, "true"),
            Response::FALSE => write!(f, "false"),
            Response::MAP(vars) => {
                let parts: Vec<String> = vars
                    .iter()
                    .map(|(name, value)| format!("{}: {}", name, value))
                    .collect();
                let line: String = parts.join(", ");
                write!(f, "{}", line)
            }
        }
    }
}

///
/// Receives inputs and executes queries against the established facts.
///
pub struct FactEngine {
    symbols: SymbolRegistry,
    facts: HashSet<Fact>,
}

impl FactEngine {
    /// Construct an instance of FactEngine.
    pub fn new() -> Self {
        Self {
            symbols: SymbolRegistry::new(),
            facts: HashSet::new(),
        }
    }

    /// Store a fact in the engine based on the statement and arguments.
    pub fn input(&mut self, stmt: &str, args: &[&str]) {
        // convert the strings into symbols and construct a Fact
        let statement: Symbol = self.symbols.value(stmt);
        let arguments: Vec<Symbol> = args.iter().map(|a| self.symbols.value(a)).collect();
        self.facts.insert(Fact::new(statement, arguments));
    }

    /// Query the fact engine based on the statement and arguments.
    pub fn query(&mut self, stmt: &str, args: &[&str]) -> Result<Vec<Response>, Error> {
        // convert the strings into symbols or variables and construct a Query
        let statement: Symbol = self.symbols.value(stmt);
        let arguments: Vec<QueryArgument> = args
            .iter()
            .map(|a| QueryArgument::from_str(&mut self.symbols, a))
            .collect();
        let query = Query::new(statement, arguments);
        // Simple approach of iterating all of the facts. Because each fact is
        // unique (any two facts with the same statement and arguments are
        // stored only once), the first 'true' match will exit the loop early.
        // Queries with one or more variable arguments means each fact will be
        // visited to find all possible matches.
        let mut responses: Vec<Response> = Vec::new();
        for fact in self.facts.iter() {
            let response = fact.matches(&mut self.symbols, &query);
            if response == Response::TRUE {
                return Ok(vec![response]);
            }
            if response.is_map() {
                responses.push(response);
            }
        }
        if responses.is_empty() {
            // no matching facts found
            Ok(vec![Response::FALSE])
        } else {
            Ok(responses)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_registry() {
        let mut symfac = SymbolRegistry::new();
        let ok = symfac.value("ok");
        assert_eq!(Some(String::from("ok")), symfac.name(&ok));
        let error = symfac.value("error");
        assert_eq!(Some(String::from("error")), symfac.name(&error));
        assert_ne!(ok, error);
        assert_eq!(ok, symfac.value("ok"));
        assert_eq!(ok, symfac.value("ok"));
    }

    #[test]
    fn test_basic_fact_matching() {
        let mut symbols = SymbolRegistry::new();

        // establish a fact
        let has_friends = symbols.value("has_friends");
        let bocchi = symbols.value("bocchi");
        let aru = symbols.value("aru");
        let args = vec![bocchi];
        let fact = Fact::new(has_friends, args);

        // matching with symbol
        let args = vec![QueryArgument::SYMBOL(bocchi)];
        let query = Query::new(has_friends, args);
        assert_eq!(fact.matches(&mut symbols, &query), Response::TRUE);

        // non-matching with symbol
        let args = vec![QueryArgument::SYMBOL(aru)];
        let query = Query::new(has_friends, args);
        assert_eq!(fact.matches(&mut symbols, &query), Response::FALSE);

        // matching with variable
        let args = vec![QueryArgument::VARIABLE("X".into())];
        let query = Query::new(has_friends, args);
        let response = fact.matches(&mut symbols, &query);
        if let Response::MAP(vars) = &response {
            assert_eq!(vars.len(), 1);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "bocchi");
        } else {
            panic!("expected a map response");
        }
    }

    #[test]
    fn test_querying_one_argument() {
        let mut engine = FactEngine::new();

        // non-matching with variable
        let result = engine.query("has_friends", &["X"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);

        // establish a fact
        engine.input("has_friends", &["bocchi"]);

        // matching with symbol
        let result = engine.query("has_friends", &["bocchi"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::TRUE);

        // non-matching symbol argument
        let result = engine.query("has_friends", &["aru"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);

        // non-matching symbol statement
        let result = engine.query("silly_person", &["aru"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);

        // matching with variable
        let result = engine.query("has_friends", &["X"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 1);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "bocchi");
        } else {
            panic!("expected a map response");
        }

        // non-matching symbol statement
        let result = engine.query("silly_person", &["O"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);
    }

    #[test]
    fn test_query_duplicate_facts() {
        let mut engine = FactEngine::new();

        // establish a fact
        engine.input("has_friends", &["bocchi"]);
        engine.input("has_friends", &["bocchi"]);
        engine.input("has_friends", &["bocchi"]);

        // matching with multiple responses
        let result = engine.query("has_friends", &["X"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 1);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "bocchi");
        } else {
            panic!("expected a map response");
        }
    }

    #[test]
    fn test_querying_multiple_responses() {
        let mut engine = FactEngine::new();

        // establish a fact
        engine.input("has_friends", &["bocchi"]);
        engine.input("has_friends", &["nako"]);
        engine.input("has_friends", &["sotoka"]);

        // matching with multiple responses
        let result = engine.query("has_friends", &["X"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 3);
        let expected = vec!["bocchi", "nako", "sotoka"];
        let mut actual: Vec<String> = Vec::new();
        for idx in 0..3 {
            if let Response::MAP(vars) = &responses[idx] {
                assert_eq!(vars.len(), 1);
                let (var, value) = &vars[0];
                assert_eq!(var, "X");
                actual.push(value.to_owned());
            } else {
                panic!("expected a map response");
            }
        }
        actual.sort();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_querying_two_arguments() {
        let mut engine = FactEngine::new();

        // non-matching with variable
        let result = engine.query("are_friends", &["X", "Y"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);

        // establish some facts
        engine.input("are_friends", &["sotoka", "kako"]);

        // non-matching
        let result = engine.query("are_friends", &["kako", "sotoka"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);

        // matching with one response * one variable
        let result = engine.query("are_friends", &["X", "kako"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 1);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "sotoka");
        } else {
            panic!("expected a map response");
        }

        // matching with one response * two variables
        let result = engine.query("are_friends", &["X", "Y"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 2);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "sotoka");
            let (var, value) = &vars[1];
            assert_eq!(var, "Y");
            assert_eq!(value, "kako");
        } else {
            panic!("expected a map response");
        }

        // additional fact
        engine.input("are_friends", &["mayo", "aru"]);

        // matching with one response * one variable
        let result = engine.query("are_friends", &["X", "kako"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 1);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "sotoka");
        } else {
            panic!("expected a map response");
        }
    }

    #[test]
    fn test_querying_repeat_vars() {
        let mut engine = FactEngine::new();

        // establish facts
        engine.input("are_friends", &["sotoka", "kako"]);
        engine.input("are_friends", &["aru", "aru"]);

        // non-matching with variable
        let result = engine.query("are_friends", &["Y", "Y"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 1);
            let (var, value) = &vars[0];
            assert_eq!(var, "Y");
            assert_eq!(value, "aru");
        } else {
            panic!("expected a map response");
        }
    }

    #[test]
    fn test_query_three_arguments() {
        let mut engine = FactEngine::new();
        engine.input("three_tuple", &["3", "4", "5"]);
        engine.input("three_tuple", &["5", "12", "13"]);

        // matching with different variables
        let result = engine.query("three_tuple", &["X", "4", "Y"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 2);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "3");
            let (var, value) = &vars[1];
            assert_eq!(var, "Y");
            assert_eq!(value, "5");
        } else {
            panic!("expected a map response");
        }

        // non-matching with duplicate variable
        let result = engine.query("three_tuple", &["X", "X", "Y"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);

        // matching with duplicate variable
        engine.input("three_tuple", &["4", "4", "5"]);
        let result = engine.query("three_tuple", &["X", "X", "Y"]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        if let Response::MAP(vars) = &responses[0] {
            assert_eq!(vars.len(), 2);
            let (var, value) = &vars[0];
            assert_eq!(var, "X");
            assert_eq!(value, "4");
            let (var, value) = &vars[1];
            assert_eq!(var, "Y");
            assert_eq!(value, "5");
        } else {
            panic!("expected a map response");
        }
    }

    #[test]
    fn test_statement_sans_arguments() {
        let mut engine = FactEngine::new();

        // establish a fact without arguments
        engine.input("is_true", &[]);

        // matching
        let result = engine.query("is_true", &[]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::TRUE);

        // non-matching
        let result = engine.query("is_false", &[]);
        assert!(result.is_ok());
        let responses = result.unwrap();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0], Response::FALSE);
    }
}
