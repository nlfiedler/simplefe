//
// Copyright 2022 Nathan Fiedler
//
use simplefe::engine::*;
use simplefe::parser::parse;
use std::io::{self, Write};

fn eval_and_print(engine: &mut FactEngine, line: &str) {
    if line.starts_with("INPUT ") {
        match parse(&line[6..]) {
            Ok(expr) => {
                let strs: Vec<&str> = expr.arguments.iter().map(|s| &**s).collect();
                engine.input(&expr.statement, &strs[..]);
            }
            Err(err) => println!("error parsing input: {}", err),
        }
    } else if line.starts_with("QUERY ") {
        match parse(&line[6..]) {
            Ok(expr) => {
                let strs: Vec<&str> = expr.arguments.iter().map(|s| &**s).collect();
                match engine.query(&expr.statement, &strs[..]) {
                    Ok(responses) => {
                        println!("---");
                        for response in responses {
                            println!("{}", response);
                        }
                    }
                    Err(err) => println!("error processing query: {}", err),
                }
            }
            Err(err) => println!("error parsing input: {}", err),
        }
    } else if line.starts_with("EXIT") {
        std::process::exit(0);
    }
}

fn main() {
    let mut engine = FactEngine::new();
    // the read-eval-print-loop
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => eval_and_print(&mut engine, &input),
            Err(err) => println!("error: {:?}", err),
        }
    }
}
