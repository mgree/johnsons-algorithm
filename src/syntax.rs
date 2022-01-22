use std::collections::HashSet;

use crate::options::DEFAULT_WIDTH;

lalrpop_mod!(parser);

#[derive(Debug)]
pub struct Program(pub Vec<Constraint>);

#[derive(Debug)]
pub enum Constraint {
    Rule(Atom, Vec<Literal>),
    Fact(Atom),
    Integrity(Vec<Literal>),
}

#[derive(Debug)]
pub enum Literal {
    Atom(Atom),
    Not(Atom),
}

#[derive(Debug)]
pub enum Atom {
    Simple(Symbol),
    Fun(Symbol, Vec<SimpleTerm>),
}

#[derive(Clone, Debug)]
pub enum SimpleTerm {
    Symbol(Symbol),
    Variable(Variable),
    Int(isize),
    /*
    // other stuff supported by clingo
    Supremum,
    Infimum,
    */
}

pub type Symbol = String;
pub type Variable = String;

impl Program {
    pub fn is_ground(&self) -> bool {
        self.0.iter().all(|c| c.is_ground())
    }

    pub fn vars(&self) -> HashSet<&Variable> {
        self.0.iter().flat_map(|c| c.vars()).collect()
    }

    pub fn parse(s: &str) -> Result<Self, String> {
        parser::ProgramParser::new()
            .parse(s)
            .map_err(|e| e.to_string())
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        pp.intersperse(self.0.iter().map(|c| c.pretty(pp)), pp.line())
    }
}

impl Constraint {
    pub fn is_ground(&self) -> bool {
        match self {
            Constraint::Rule(head, body) => head.is_ground() && body.iter().all(|l| l.is_ground()),
            Constraint::Fact(head) => head.is_ground(),
            Constraint::Integrity(ls) => ls.iter().all(|l| l.is_ground()),
        }
    }

    pub fn vars(&self) -> HashSet<&Variable> {
        match self {
            Constraint::Rule(head, body) => body
                .iter()
                .flat_map(|l| l.vars())
                .chain(head.vars())
                .collect(),
            Constraint::Fact(head) => head.vars(),
            Constraint::Integrity(ls) => ls.iter().flat_map(|l| l.vars()).collect(),
        }
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Constraint::Rule(head, body) => head
                .pretty(pp)
                .append(pp.space())
                .append(":-")
                .append(pp.space())
                .append(
                    pp.intersperse(
                        body.iter().map(|l| l.pretty(pp)),
                        pp.text(",").append(pp.line()),
                    )
                    .nest(3)
                    .group(),
                )
                .append("."),
            Constraint::Fact(head) => head.pretty(pp).append("."),
            Constraint::Integrity(body) => pp
                .text(":-")
                .append(pp.space())
                .append(
                    pp.intersperse(
                        body.iter().map(|l| l.pretty(pp)),
                        pp.text(",").append(pp.line()),
                    )
                    .nest(3)
                    .group(),
                )
                .append("."),
        }
    }
}

impl Literal {
    pub fn is_positive(&self) -> bool {
        match self {
            Literal::Atom(..) => true,
            Literal::Not(..) => false,
        }
    }

    pub fn is_ground(&self) -> bool {
        match self {
            Literal::Atom(a) | Literal::Not(a) => a.is_ground(),
        }
    }

    pub fn vars(&self) -> HashSet<&Variable> {
        match self {
            Literal::Atom(a) | Literal::Not(a) => a.vars(),
        }
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Literal::Atom(atom) => atom.pretty(pp),
            Literal::Not(atom) => pp.text("not").append(pp.space()).append(atom.pretty(pp)),
        }
    }
}

impl Atom {
    pub fn is_ground(&self) -> bool {
        match self {
            Atom::Simple(..) => true,
            Atom::Fun(_f, args) => args.iter().all(|t| t.is_ground()),
        }
    }

    pub fn vars(&self) -> HashSet<&Variable> {
        match self {
            Atom::Simple(..) => HashSet::new(),
            Atom::Fun(_f, args) => args.iter().flat_map(|arg| arg.vars()).collect(),
        }
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Atom::Simple(sym) => pp.text(sym),
            Atom::Fun(f, args) => pp
                .text(f)
                .append("(")
                .append(
                    pp.intersperse(
                        args.iter().map(|arg| arg.pretty(pp)),
                        pp.text(",").append(pp.line()),
                    )
                    .nest(1)
                    .group(),
                )
                .append(")"),
        }
    }
}

impl SimpleTerm {
    pub fn is_ground(&self) -> bool {
        match self {
            SimpleTerm::Symbol(..) | SimpleTerm::Int(..) => true,
            SimpleTerm::Variable(..) => false,
        }
    }

    pub fn vars(&self) -> HashSet<&Variable> {
        match self {
            SimpleTerm::Symbol(..) | SimpleTerm::Int(..) => HashSet::new(),
            SimpleTerm::Variable(v) => HashSet::from([v]),
        }
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            SimpleTerm::Symbol(sym) => pp.text(sym),
            SimpleTerm::Variable(v) => pp.text(v),
            SimpleTerm::Int(n) => pp.text(n.to_string()),
        }
    }
}

macro_rules! pretty_Display {
    ($T:ty) => {
        impl std::fmt::Display for $T {
            /// Macro-generated Display instance using the .pretty() method.
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let pp = pretty::BoxAllocator;
                let doc = self.pretty::<_, ()>(&pp);
                doc.1.render_fmt(DEFAULT_WIDTH, f)
            }
        }
    };
}
pretty_Display!(Program);
pretty_Display!(Constraint);
pretty_Display!(Literal);
pretty_Display!(Atom);
pretty_Display!(SimpleTerm);
