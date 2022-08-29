use std::fs;

mod ast;
mod core;
mod db;
mod elaboration;
mod lexer;
mod parser;

use elaboration::elaborate;
use parser::{parse_program, ProgramSource};

#[salsa::jar(db = Db)]
pub struct Jar(parser::ProgramSource, ast::Id, ast::Program);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB: ?Sized + salsa::DbWithJar<Jar>> Db for DB {}

fn main() {
    let mut db = db::Database::default();
    let s = fs::read_to_string("input").expect("Failed to read input file");
    let s = ProgramSource::new(&mut db, s);
    let program = parse_program(&db, s).expect("Failed to parse");
    // let (_term, _ty) = elaborate(&db, &raw_term).expect("Failed to elaborate");
}
