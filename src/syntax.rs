use std::collections::HashSet;

use crate::options::DEFAULT_WIDTH;

lalrpop_mod!(
    #[allow(clippy::all)]
    parser
);

#[derive(Debug)]
pub struct Program(pub Vec<Constraint>);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
    Rule(Atom, Vec<Literal>),
    Fact(Atom),
    Integrity(Vec<Literal>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Literal {
    Atom(Atom),
    Not(Atom),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Atom {
    pub f: Symbol,
    pub args: Vec<SimpleTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Relation(usize),
    Constant,
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
    pub fn as_atom(&self) -> &Atom {
        match self {
            Literal::Atom(a) | Literal::Not(a) => a,
        }
    }

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
    pub fn from<T: AsRef<str>>(f: T, args: &[SimpleTerm]) -> Atom {
        Atom {
            f: f.as_ref().to_string(),
            args: Vec::from(args),
        }
    }

    pub fn is_ground(&self) -> bool {
        self.args.iter().all(|t| t.is_ground())
    }

    pub fn vars(&self) -> HashSet<&Variable> {
        self.args.iter().flat_map(|arg| arg.vars()).collect()
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        if self.args.is_empty() {
            pp.text(&self.f)
        } else {
            pp.text(&self.f)
                .append("(")
                .append(
                    pp.intersperse(
                        self.args.iter().map(|arg| arg.pretty(pp)),
                        pp.text(",").append(pp.line()),
                    )
                    .nest(1)
                    .group(),
                )
                .append(")")
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

impl Type {
    pub fn is_relation(&self) -> bool {
        match self {
            Type::Relation(..) => true,
            Type::Constant => false,
        }
    }

    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Type::Relation(arity) => pp.text(format!("relation({})", arity)),
            Type::Constant => pp.text("constant"),
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
pretty_Display!(Type);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn reach_not_grounded() {
        let p = Program::parse(concat!(
            "edge(a,b).\n",
            "edge(a,c).\t\r\n",
            "edge(b,d).  ",
            "edge(c,d).\n",
            "reach(X, Y) :- edge(X, Y).",
            "reach(X, Z) :- edge(X, Y), reach(Y, Z)."
        ))
        .expect("ok parse");

        assert!(!p.is_ground());
        assert_eq!(
            p.vars(),
            HashSet::from([&"X".to_string(), &"Y".to_string(), &"Z".to_string()])
        );
    }
}
