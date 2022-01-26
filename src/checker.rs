use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::Extend;

use crate::syntax::*;

// TODO use unification to globally figure out the types of each relation

#[derive(Debug, thiserror::Error)]
pub enum Error<'a> {
    #[error("the variable `{0}` doesn't occur positively in `{1}`")]
    NonPositiveVariable(&'a Variable, &'a Constraint),
    #[error("the variable `{0}` occurs in the fact `{1}`")]
    VariableInFact(&'a Variable, &'a Atom),
    #[error("the atom `{0}` should have arity `{1}`")]
    ArityMismatch(&'a Atom, usize),
    #[error("the atom `{0}` was used as a relation, but it has type `{1}`")]
    AppliedNonRelation(&'a Atom, Type),
    #[error("the symbol `{0}` was used as a constant, but it has type `{1}`")]
    RelationAsConstant(&'a Symbol, Type),
}

#[derive(Debug)]
pub struct Checker<'a> {
    program: &'a Program,
    pub types: HashMap<Symbol, Type>,
    pub refs: HashMap<Symbol, HashSet<(Symbol, bool)>>,
    pub backrefs: HashMap<Symbol, HashSet<(Symbol, bool)>>,
    // TODO: build the backreference graph on ATOMS using this as a guide
    pub atoms: Vec<&'a Atom>,
}

impl<'a> Checker<'a> {
    pub fn new(program: &'a Program) -> Result<Checker<'_>, Vec<Error<'_>>> {
        // using btrees for reliable atom ordering
        let all_atoms: BTreeSet<_> = program
            .0
            .iter()
            .flat_map::<BTreeSet<&'a Atom>, _>(|c| match c {
                Constraint::Rule(head, body) => body
                    .iter()
                    .map(|l| l.as_atom())
                    .chain(std::iter::once(head))
                    .collect(),
                Constraint::Fact(head) => std::iter::once(head).collect(),
                Constraint::Integrity(body) => body.iter().map(|l| l.as_atom()).collect(),
            })
            .collect();

        let mut checker = Checker {
            program,
            types: HashMap::new(),
            refs: HashMap::new(),
            backrefs: HashMap::new(),
            atoms: all_atoms.into_iter().collect(),
        };

        let errors = checker.check_program();

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(checker)
    }

    pub fn show_refs(&self) -> String {
        let mut s = String::new();
        s.push_str("digraph {\n  ");

        for (sym, ty) in &self.types {
            if ty.is_relation() {
                s.push_str(sym);
                s.push_str("; ");
            }
        }

        s.push_str("\n\n  // forward references\n");
        for (src, tgts) in &self.refs {
            for (tgt, polarity) in tgts {
                s.push_str("  ");
                s.push_str(src);
                s.push_str(" -> ");
                s.push_str(tgt);
                s.push_str(" [label=\"");
                s.push(if *polarity { '+' } else { '-' });
                s.push_str("\"];\n")
            }
        }

        s.push_str("}\n");
        s
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
                // check the parts
                let mut errors = self.check_atom(head);
                errors.extend(body.iter().flat_map(|l| self.check_literal(Some(head), l)));

                // positivity/safety checks
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
                // check the parts
                let mut errors: Vec<_> = ls
                    .iter()
                    .flat_map(|l| self.check_literal(None, l))
                    .collect();

                // positivity/safety checks
                let all_vars: HashSet<_> = ls.iter().flat_map(|l| l.vars()).collect();
                let pos_vars = ls
                    .iter()
                    .filter(|l| l.is_positive())
                    .flat_map(|l| l.vars())
                    .collect();
                let unsafe_vars = all_vars.difference(&pos_vars);
                errors.extend(unsafe_vars.map(|v| Error::NonPositiveVariable(v, c)));

                errors
            }
            Constraint::Fact(head) => {
                // check the parts
                let mut errors = self.check_atom(head);

                // positivity/safety check (specialized)
                errors.extend(head.vars().iter().map(|v| Error::VariableInFact(v, head)));

                errors
            }
        }
    }

    fn check_literal(&mut self, h: Option<&'a Atom>, l: &'a Literal) -> Vec<Error<'a>> {
        // record references
        if let Some(h) = h {
            let a = l.as_atom();
            let polarity = l.is_positive();

            let forward = (a.f.clone(), polarity);
            match self.refs.get_mut(&h.f) {
                Some(atoms) => {
                    atoms.insert(forward);
                }
                None => {
                    self.refs.insert(h.f.clone(), HashSet::from([forward]));
                }
            };
            let backward = (h.f.clone(), polarity);
            match self.backrefs.get_mut(&a.f) {
                Some(atoms) => {
                    atoms.insert(backward);
                }
                None => {
                    self.backrefs.insert(a.f.clone(), HashSet::from([backward]));
                }
            };
        }

        self.check_atom(l.as_atom())
    }

    fn check_atom(&mut self, a: &'a Atom) -> Vec<Error<'a>> {
        // arity check
        let got_arity = a.args.len();

        let mut errors = match self.types.get(&a.f) {
            Some(Type::Relation(expected_arity)) if *expected_arity != got_arity => {
                vec![Error::ArityMismatch(a, *expected_arity)]
            }
            Some(Type::Relation(..)) => vec![],
            Some(t) => vec![Error::AppliedNonRelation(a, *t)],
            None => {
                self.types.insert(a.f.clone(), Type::Relation(got_arity));
                vec![]
            }
        };

        // check each term (type checks, etc.)
        errors.extend(a.args.iter().flat_map(|t| self.check_term(t)));

        errors
    }

    fn check_term(&mut self, t: &'a SimpleTerm) -> Vec<Error<'a>> {
        match t {
            SimpleTerm::Variable(..) | SimpleTerm::Int(..) => vec![],
            SimpleTerm::Symbol(sym) => match self.types.get(sym) {
                Some(t @ Type::Relation(..)) => {
                    vec![Error::RelationAsConstant(sym, *t)]
                }
                Some(Type::Constant) => vec![],
                None => {
                    self.types.insert(sym.clone(), Type::Constant);
                    vec![]
                }
            },
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

    #[test]
    fn bad_arity_unsafe() {
        let p = Program::parse("f(a). f(b, c).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 1);

        match &errors[0] {
            Error::ArityMismatch(a, expected) => {
                match &p.0[1] {
                    Constraint::Fact(a2) => assert_eq!(a, &a2),
                    c => panic!("unexpected constraint {} in error", c),
                };

                assert_eq!(*expected, 1);
            }
            e => panic!("unexpected error {:?}", e),
        };
    }

    #[test]
    fn relation_as_constant() {
        let p = Program::parse("f(1). g(1) :- g(f).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 1);

        match &errors[0] {
            Error::RelationAsConstant(sym, ty) => {
                assert_eq!(sym.as_str(), "f");
                assert_eq!(ty, &Type::Relation(1));
            }
            e => panic!("unexpected error {:?}", e),
        };
    }

    #[test]
    fn relation_as_constant_integrity() {
        let p = Program::parse("f(1). :- not g(f).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 1);

        match &errors[0] {
            Error::RelationAsConstant(sym, ty) => {
                assert_eq!(sym.as_str(), "f");
                assert_eq!(ty, &Type::Relation(1));
            }
            e => panic!("unexpected error {:?}", e),
        };
    }

    #[test]
    fn applied_non_relation() {
        let p = Program::parse("f(a). a(2).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 1);

        match &errors[0] {
            Error::AppliedNonRelation(a, ty) => {
                match &p.0[1] {
                    Constraint::Fact(a2) => assert_eq!(a, &a2),
                    c => panic!("unexpected constraint {} in error", c),
                };
                assert_eq!(ty, &Type::Constant);
            }
            e => panic!("unexpected error {:?}", e),
        };
    }

    #[test]
    fn applied_non_relation_rule() {
        let p = Program::parse("f(a). f(b) :- a(2).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 1);

        match &errors[0] {
            Error::AppliedNonRelation(a, ty) => {
                match &p.0[1] {
                    Constraint::Rule(_, ls) => {
                        assert_eq!(ls.len(), 1);
                        assert_eq!(a, &ls[0].as_atom());
                    }
                    c => panic!("unexpected constraint {} in error", c),
                };
                assert_eq!(ty, &Type::Constant);
            }
            e => panic!("unexpected error {:?}", e),
        };
    }

    #[test]
    fn applied_non_relation_integrity() {
        let p = Program::parse("f(a). :- a(2).").expect("correct parse");

        let errors = Checker::new(&p).expect_err("safety violation");
        assert!(!errors.is_empty());
        assert!(errors.len() == 1);

        match &errors[0] {
            Error::AppliedNonRelation(a, ty) => {
                match &p.0[1] {
                    Constraint::Integrity(ls) => {
                        assert_eq!(ls.len(), 1);
                        assert_eq!(a, &ls[0].as_atom());
                    }
                    c => panic!("unexpected constraint {} in error", c),
                };
                assert_eq!(ty, &Type::Constant);
            }
            e => panic!("unexpected error {:?}", e),
        };
    }
}
