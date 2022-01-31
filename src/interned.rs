use std::collections::HashSet;

use crate::circuits::Graph;
use crate::formula::Formula;
use crate::syntax;

#[derive(Clone, Debug)]
pub struct Program<'a> {
    pub constraints: Vec<Constraint>,
    pub atoms: Vec<&'a syntax::Atom>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
    Rule(IAtom, Vec<Literal>),
    Fact(IAtom),
    Integrity(Vec<Literal>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Literal {
    Atom(IAtom),
    Not(IAtom),
}

pub type IAtom = usize;

impl<'a> Program<'a> {
    pub fn clark_completion(&self) -> Formula<&'a syntax::Atom> {
        todo!()
    }

    /// Positive dependencies of _atoms_:
    ///
    /// ```asp
    /// a(1,2) :- b(1), c(2)
    ///
    /// creates edges from `a(1,2)` to `b(1)` and `c(2)`
    ///
    /// Circuits in this graph generate loop formulae.
    pub fn graph(&self) -> Graph {
        let mut backrefs = vec![HashSet::new(); self.atoms.len()];

        for c in self.constraints.iter() {
            if let Constraint::Rule(head, body) = c {
                for l in body {
                    if let Some(a) = l.as_positive_atom() {
                        backrefs[*head].insert(a);
                    }
                }
            }
        }

        backrefs.into_iter().enumerate().collect()
    }

    /// Given a logic program P (`self`) and a loop (`cycle`), returns the literals G_ij and atoms
    // TODO: refactor to use some notion of formula
    pub fn loop_formula(&self, cycle: &[IAtom]) -> Formula<&'a syntax::Atom> {
        let mut neg = Vec::new();

        for constraint in self.constraints.iter() {
            match constraint {
                Constraint::Rule(head, ls) => {
                    if cycle.contains(head) {
                        if ls
                            .iter()
                            .filter_map(|l| l.as_positive_atom())
                            .any(|a| cycle.contains(&a))
                        {
                            continue;
                        }
                        neg.extend(ls.clone());
                    }
                }
                Constraint::Fact(..) | Constraint::Integrity(..) => (),
            }
        }

        let mut cycle = Vec::from(cycle);
        assert_eq!(cycle[0], cycle[cycle.len() - 1]);
        cycle.pop();

        Formula::implies(
            Formula::ands(neg.into_iter().map(|l| match l {
                Literal::Not(a) => Formula::Proposition(self.atoms[a]),
                Literal::Atom(a) => Formula::not(Formula::Proposition(self.atoms[a])),
            })),
            Formula::ands(
                cycle
                    .into_iter()
                    .map(|a| Formula::not(Formula::Proposition(self.atoms[a]))),
            ),
        )
    }

    /// Computes R^+ and R^- from Lin and Zhao (AI 2004).
    pub fn loop_partition(&self, cycle: &[IAtom]) -> (Program, Program) {
        let mut pos = Program {
            constraints: Vec::new(),
            atoms: self.atoms.clone(),
        };
        let mut neg = Program {
            constraints: Vec::new(),
            atoms: self.atoms.clone(),
        };

        for constraint in self.constraints.iter() {
            match constraint {
                Constraint::Rule(head, ls) => {
                    if cycle.contains(head) {
                        if ls
                            .iter()
                            .filter_map(|l| l.as_positive_atom())
                            .any(|a| cycle.contains(&a))
                        {
                            pos.constraints.push(constraint.clone());
                        } else {
                            neg.constraints.push(constraint.clone());
                        }
                    }
                }
                Constraint::Fact(head) => {
                    if cycle.contains(head) {
                        neg.constraints.push(constraint.clone());
                    }
                }
                Constraint::Integrity(..) => (),
            }
        }

        (pos, neg)
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        pp.intersperse(
            self.constraints
                .iter()
                .map(|c| self.pretty_constraint(pp, c)),
            pp.line(),
        )
    }

    pub fn pretty_constraint<'b, D, A>(
        &'b self,
        pp: &'b D,
        c: &Constraint,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match c {
            Constraint::Rule(head, body) => self
                .pretty_atom(pp, *head)
                .append(pp.space())
                .append(":-")
                .append(pp.space())
                .append(
                    pp.intersperse(
                        body.iter().map(|l| self.pretty_literal(pp, l)),
                        pp.text(",").append(pp.line()),
                    )
                    .nest(3)
                    .group(),
                )
                .append("."),
            Constraint::Fact(head) => self.pretty_atom(pp, *head).append("."),
            Constraint::Integrity(body) => pp
                .text(":-")
                .append(pp.space())
                .append(
                    pp.intersperse(
                        body.iter().map(|l| self.pretty_literal(pp, l)),
                        pp.text(",").append(pp.line()),
                    )
                    .nest(3)
                    .group(),
                )
                .append("."),
        }
    }

    pub fn pretty_literal<'b, D, A>(
        &'b self,
        pp: &'b D,
        l: &Literal,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match l {
            Literal::Atom(atom) => self.pretty_atom(pp, *atom),
            Literal::Not(atom) => pp
                .text("not")
                .append(pp.space())
                .append(self.pretty_atom(pp, *atom)),
        }
    }

    pub fn pretty_atom<'b, D, A>(&'b self, pp: &'b D, a: IAtom) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.atoms[a].pretty(pp)
    }
}

impl Literal {
    pub fn as_positive_atom(&self) -> Option<IAtom> {
        match self {
            Literal::Atom(a) => Some(*a),
            Literal::Not(..) => None,
        }
    }
}

impl<'a> From<&'a syntax::Program> for Program<'a> {
    fn from(p: &'a syntax::Program) -> Program<'a> {
        debug_assert!(p.is_ground(), "tried to intern non-ground program");

        let atoms = p.atoms();

        // avoid annoying move rules around functions
        macro_rules! anum {
            ($a:expr) => {
                atoms.binary_search($a).expect("known atom")
            };
        }

        macro_rules! lit {
            ($l:expr) => {
                match $l {
                    syntax::Literal::Atom(a) => Literal::Atom(anum!(&a)),
                    syntax::Literal::Not(a) => Literal::Not(anum!(&a)),
                }
            };
        }

        let constraints =
            p.0.iter()
                .map(|c| match c {
                    syntax::Constraint::Rule(head, body) => {
                        Constraint::Rule(anum!(&head), body.iter().map(|l| lit!(l)).collect())
                    }
                    syntax::Constraint::Fact(head) => Constraint::Fact(anum!(&head)),
                    syntax::Constraint::Integrity(body) => {
                        Constraint::Integrity(body.iter().map(|l| lit!(l)).collect())
                    }
                })
                .collect();

        Program { constraints, atoms }
    }
}

impl<'a> std::fmt::Display for Program<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(crate::options::DEFAULT_WIDTH, f)
    }
}

#[cfg(test)]
mod test_partition {
    use super::*;
    use crate::circuits;

    #[test]
    fn lin_zhao_eg_text_p119() {
        let p = syntax::Program::parse("a :- b. b :- a. a.").expect("valid parse");
        let p = Program::from(&p);

        let graph = p.graph();
        let circuits = circuits::find(&graph);
        assert_eq!(circuits.len(), 1);

        let (pos, neg) = p.loop_partition(&circuits[0]);

        // order dependent :(
        assert_eq!(pos.constraints.len(), 2);
        assert_eq!(pos.constraints[0], p.constraints[0]);
        assert_eq!(pos.constraints[1], p.constraints[1]);

        assert_eq!(neg.constraints.len(), 1);
        assert_eq!(neg.constraints[0], p.constraints[2]);
    }

    #[test]
    fn lin_zhao_eg1_p120() {
        let p = syntax::Program::parse(concat!(
            "a :- b. b :- a. a :- not c.\n",
            "c :- d. d :- c. c :- not a."
        ))
        .expect("valid parse");
        let p = Program::from(&p);

        let graph = p.graph();
        let circuits = circuits::find(&graph);
        assert_eq!(circuits.len(), 2);

        // the asserts below are very much order dependent!!!

        // circuit 0
        let (pos, neg) = p.loop_partition(&circuits[0]);

        assert_eq!(pos.constraints.len(), 2);
        assert_eq!(pos.constraints[0], p.constraints[0]);
        assert_eq!(pos.constraints[1], p.constraints[1]);
        assert_eq!(neg.constraints.len(), 1);
        assert_eq!(neg.constraints[0], p.constraints[2]);

        // circuit 1
        let (pos, neg) = p.loop_partition(&circuits[1]);

        assert_eq!(pos.constraints.len(), 2);
        assert_eq!(pos.constraints[0], p.constraints[3]);
        assert_eq!(pos.constraints[1], p.constraints[4]);
        assert_eq!(neg.constraints.len(), 1);
        assert_eq!(neg.constraints[0], p.constraints[5]);
    }

    #[test]
    fn lin_zhao_eg2_p120() {
        let p = syntax::Program::parse(concat!(
            "a :- b. b :- a. a :- not c.\n",
            "c :- d. d :- c. c :- not a."
        ))
        .expect("valid parse");
        let p = Program::from(&p);

        let graph = p.graph();
        let circuits = circuits::find(&graph);
        assert_eq!(circuits.len(), 2);

        // the asserts below are very much order dependent!!!

        // circuit 0
        let phi0 = p.loop_formula(&circuits[0]);
        assert_eq!(
            phi0,
            Formula::implies(
                Formula::Proposition(&syntax::Atom::from("c", &[])),
                Formula::and(
                    Formula::not(Formula::Proposition(&syntax::Atom::from("a", &[]))),
                    Formula::not(Formula::Proposition(&syntax::Atom::from("b", &[])))
                )
            )
        );

        // circuit 1
        let phi1 = p.loop_formula(&circuits[1]);
        assert_eq!(
            phi1,
            Formula::implies(
                Formula::Proposition(&syntax::Atom::from("a", &[])),
                Formula::and(
                    Formula::not(Formula::Proposition(&syntax::Atom::from("c", &[]))),
                    Formula::not(Formula::Proposition(&syntax::Atom::from("d", &[])))
                )
            )
        );
    }
}
