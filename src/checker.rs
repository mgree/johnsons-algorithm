use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::Extend;

use crate::syntax::*;

pub enum Error<'a> {
    NonPositiveVariable(&'a Variable, &'a Constraint),
    VariableInFact(&'a Variable, &'a Atom),
    ArityMismatch(&'a Atom, usize),
    ExpectedBoolean(&'a SimpleTerm, &'a Atom),
}

#[derive(Debug)]
pub struct Checker<'a> {
    program: &'a Program,
    types: HashMap<Symbol, usize>,
}

impl<'a> Checker<'a> {
    pub fn new(program: &'a Program) -> Result<Checker<'_>, Vec<Error<'_>>> {
        let mut checker = Checker {
            program,
            types: HashMap::new(),
        };

        let errors = checker.check_program();

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(checker)
    }

    fn check_program(&mut self) -> Vec<Error<'a>> {
        self.program
            .0
            .iter()
            .flat_map(|c| self.check_constraint(c))
            .collect()
    }

    fn check_constraint(&mut self, c: &'a Constraint) -> Vec<Error<'a>> {
        match c {
            Constraint::Rule(head, body) => {
                let mut errors = self.check_atom(head);

                let mut all_vars = head.vars();
                all_vars.extend(body.iter().flat_map(|l| l.vars()));

                let pos_vars = body
                    .iter()
                    .filter(|l| l.is_positive())
                    .flat_map(|l| l.vars())
                    .collect();

                let unsafe_vars = all_vars.difference(&pos_vars);

                errors.extend(unsafe_vars.map(|v| Error::NonPositiveVariable(v, c)));

                errors
            }
            Constraint::Integrity(ls) => {
                let all_vars: HashSet<_> = ls.iter().flat_map(|l| l.vars()).collect();

                let pos_vars = ls
                    .iter()
                    .filter(|l| l.is_positive())
                    .flat_map(|l| l.vars())
                    .collect();

                let unsafe_vars = all_vars.difference(&pos_vars);

                unsafe_vars
                    .map(|v| Error::NonPositiveVariable(v, c))
                    .collect()
            }
            Constraint::Fact(head) => {
                let mut errors = self.check_atom(head);

                errors.extend(head.vars().iter().map(|v| Error::VariableInFact(v, head)));

                errors
            }
        }
    }

    fn check_atom(&mut self, a: &'a Atom) -> Vec<Error<'a>> {
        let got_arity = a.args.len();

        match self.types.get(&a.f) {
            Some(expected_arity) if *expected_arity != got_arity => {
                vec![Error::ArityMismatch(a, *expected_arity)]
            }
            Some(_) => Vec::new(),
            None => {
                self.types.insert(a.f.clone(), got_arity);
                Vec::new()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn is_safe(s: &str) {
        let p = Program::parse(s).expect("correct parse");
        let c = Checker::new(&p);

        assert!(c.is_ok())
    }

    #[test]
    fn reach_ok() {
        is_safe(concat!(
            "edge(1,2). edge(2,3). edge(3,4). edge(4,1).",
            "reach(X,Y) :- edge(X,Y).",
            "reach(X,Z) :- edge(X,Y), reach(Y,Z)."
        ));
    }

    #[test]
    fn loop_ok() {
        is_safe("a :- b. b :- a.");
    }

    #[test]
    fn twomodels_ok() {
        is_safe(concat!(
            "a :- b. b :- a. a :- not c.",
            "c :- d. d :- c. c :- not a."
        ));
    }

    #[test]
    fn wildcard_ok() {
        is_safe(concat!("a(1,2). a(3,4).", "a(X,Y) :- a(X, _), a(Y, _)."))
    }

    #[test]
    fn all_vars_unsafe() {
        let p = Program::parse("f(X, Y).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 2);

        assert!(errors.iter().all(|e| match e {
            Error::VariableInFact(v, _) => v.as_str() == "X" || v.as_str() == "Y",
            _ => false,
        }));
    }
}
