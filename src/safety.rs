use std::collections::HashSet;
use std::iter::Extend;

use crate::syntax::*;

pub enum Error<'a> {
    NonPositiveVariable(&'a Variable, &'a Constraint),
    VariableInFact(&'a Variable, &'a Head),
}

impl Program {
    pub fn safety_errors(&self) -> Vec<Error<'_>> {
        self.0.iter().flat_map(|c| c.safety_errors()).collect()
    }
}

impl Constraint {
    pub fn safety_errors(&self) -> Vec<Error<'_>> {
        match self {
            Constraint::Rule(head, body) => {
                let mut all_vars = head.vars();
                all_vars.extend(body.iter().flat_map(|l| l.vars()));

                let pos_vars = body
                    .iter()
                    .filter(|l| l.is_positive())
                    .flat_map(|l| l.vars())
                    .collect();

                let unsafe_vars = all_vars.difference(&pos_vars);

                unsafe_vars
                    .map(|v| Error::NonPositiveVariable(v, self))
                    .collect()
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
                    .map(|v| Error::NonPositiveVariable(v, self))
                    .collect()
            }
            Constraint::Fact(head) => head
                .vars()
                .iter()
                .map(|v| Error::VariableInFact(v, head))
                .collect(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn is_safe(s: &str) {
        let p = Program::parse(s).expect("correct parse");

        assert!(p.safety_errors().is_empty())
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

        let errors = p.safety_errors();
        assert!(!errors.is_empty());
        assert!(errors.len() == 2);

        assert!(errors.iter().all(|e| match e {
            Error::VariableInFact(v, _) => v.as_str() == "X" || v.as_str() == "Y",
            _ => false,
        }));
    }
}
