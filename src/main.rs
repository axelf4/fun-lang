use std::fs;

mod ast;
mod core;
mod db;
mod elaboration;
mod lexer;
mod parser;

use parser::{parse_program, ProgramSource};

#[salsa::jar(db = Db)]
pub struct Jar(
    parser::ProgramSource,
    parser::parse_program,
    ast::Id,
    ast::Program,
    elaboration::elaborate,
    elaborate_program,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB: ?Sized + salsa::DbWithJar<Jar>> Db for DB {}

#[salsa::tracked]
fn elaborate_program(
    db: &dyn crate::Db,
    program: ast::Program,
) -> Result<core::Program, elaboration::Error> {
    let defs = program
        .defs(db)
        .iter()
        .map(|(name, _def)| elaboration::elaborate(db, program, *name))
        .collect::<Result<_, elaboration::Error>>()?;
    Ok(core::Program { defs })
}

fn main() {
    let mut db = db::Database::default();
    let s = fs::read_to_string("input").expect("Failed to read input file");
    let s = ProgramSource::new(&mut db, s);
    let program = parse_program(&db, s).expect("Failed to parse");
    println!("Program: {:?}", program.defs(&db));
    let program = elaborate_program(&db, program).expect("Failed to elaborate");
    println!("Program: {:?}", program);
}
