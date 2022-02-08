use std::fs;

mod ast;
mod core;
mod elaboration;
mod interpreter;
mod lexer;
mod parser;

use elaboration::elaborate;
use lexer::Lexer;
use parser::parse;

fn main() {
    let s = fs::read_to_string("input").expect("Failed to read input file");
    let raw_term = parse(Lexer::new(&s)).expect("Failed to parse");
    let (_term, _ty) = elaborate(&raw_term).expect("Failed to elaborate");
}
