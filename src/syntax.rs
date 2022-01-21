use crate::options::DEFAULT_WIDTH;

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
    Fun(Variable, Vec<SimpleTerm>),
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

impl Head {
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Head::Simple(sym) => pp.text(sym),
            Head::Fun(f, args) => pp
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

impl Atom {
    pub fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        match self {
            Atom::Simple(t) => t.pretty(pp),
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
pretty_Display!(Head);
pretty_Display!(Atom);
pretty_Display!(SimpleTerm);
