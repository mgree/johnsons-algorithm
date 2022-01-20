//use std::fmt::Display;

lalrpop_mod!(parser);

#[derive(Debug)]
pub struct Program(pub Vec<Constraint>);

#[derive(Debug)]
pub enum Constraint {
    Rule(Head, Vec<Literal>),
    Fact(Head),
    Integrity(Vec<Literal>),
}

#[derive(Debug)]
pub enum Literal {
    Atom(Atom),
    Not(Atom),
}

#[derive(Debug)]
pub enum Head {
    Simple(Symbol),
    Fun(Variable, Vec<SimpleTerm>)
}

#[derive(Debug)]
pub enum Atom {
    Simple(SimpleTerm),
    Fun(Variable, Vec<SimpleTerm>),
}

#[derive(Debug)]
pub enum SimpleTerm {
    Symbol(Symbol),
    Variable(Variable),
    /*
    // other stuff supported by clingo
    FreshVar(),
    Int(isize),
    Supremum,
    Infimum,
    */
}

pub type Symbol = String;
pub type Variable = String;

impl Program {
    pub fn parse(s: &str) -> Result<Self, String> {
        parser::ProgramParser::new()
            .parse(s)
            .map_err(|e| e.to_string())
    }
}

// TODO: pretty
