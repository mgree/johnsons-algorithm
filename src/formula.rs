#[derive(Clone, Debug, std::hash::Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Formula<A> {
    Proposition(A),
    And(Box<Formula<A>>, Box<Formula<A>>),
    Or(Box<Formula<A>>, Box<Formula<A>>),
    Implies(Box<Formula<A>>, Box<Formula<A>>),
    Iff(Box<Formula<A>>, Box<Formula<A>>),
    Not(Box<Formula<A>>),
    True,
    False,
}

impl<A> Formula<A> {
    pub fn implies(phi: Formula<A>, psi: Formula<A>) -> Formula<A> {
        match (phi, psi) {
            (Formula::True, psi) => psi,
            (Formula::False, _) => Formula::True,
            (_, Formula::True) => Formula::True,
            (phi, Formula::False) => Formula::not(phi),
            (phi, psi) => Formula::Implies(Box::new(phi), Box::new(psi)),
        }
    }

    pub fn iff(phi: Formula<A>, psi: Formula<A>) -> Formula<A> {
        match (phi, psi) {
            (Formula::True, f) | (f, Formula::True) => f,
            (Formula::False, f) | (f, Formula::False) => Formula::not(f),
            (phi, psi) => Formula::Iff(Box::new(phi), Box::new(psi)),
        }
    }

    pub fn or(phi: Formula<A>, psi: Formula<A>) -> Formula<A> {
        match (phi, psi) {
            (Formula::True, _) | (_, Formula::True) => Formula::True,
            (Formula::False, f) | (f, Formula::False) => f,
            (phi, psi) => Formula::Or(Box::new(phi), Box::new(psi)),
        }
    }

    pub fn and(phi: Formula<A>, psi: Formula<A>) -> Formula<A> {
        match (phi, psi) {
            (Formula::True, f) | (f, Formula::True) => f,
            (Formula::False, _) | (_, Formula::False) => Formula::False,
            (phi, psi) => Formula::And(Box::new(phi), Box::new(psi)),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn not(phi: Formula<A>) -> Formula<A> {
        match phi {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            Formula::Not(psi) => *psi,
            phi => Formula::Not(Box::new(phi)),
        }
    }

    pub fn ands<T: IntoIterator<Item = Formula<A>>>(phis: T) -> Formula<A> {
        phis.into_iter()
            .reduce(|phi, psi| Formula::and(phi, psi))
            .unwrap_or(Formula::True)
    }

    pub fn or_mut(&mut self, phi: Self) {
        let old = std::mem::replace(self, Formula::False);
        *self = Formula::or(old, phi)
    }
}

impl<A: std::fmt::Display> Formula<A> {
    pub fn pretty<'b, D, B>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, B>
    where
        D: pretty::DocAllocator<'b, B>,
        D::Doc: Clone,
        B: Clone,
    {
        self.pretty_imp(pp)
    }

    fn pretty_imp<'b, D, B>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, B>
    where
        D: pretty::DocAllocator<'b, B>,
        D::Doc: Clone,
        B: Clone,
    {
        match self {
            Formula::Implies(phi1, phi2) => pp.intersperse(
                [
                    phi1.pretty_or(pp).nest(2).group(),
                    pp.text("⇒"),
                    phi2.pretty_or(pp).nest(2).group(),
                ],
                pp.space(),
            ),
            Formula::Iff(phi1, phi2) => pp.intersperse(
                [
                    phi1.pretty_or(pp).nest(2).group(),
                    pp.text("≡"),
                    phi2.pretty_or(pp).nest(2).group(),
                ],
                pp.space(),
            ),
            _ => self.pretty_or(pp),
        }
    }

    fn pretty_or<'b, D, B>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, B>
    where
        D: pretty::DocAllocator<'b, B>,
        D::Doc: Clone,
        B: Clone,
    {
        match self {
            Formula::Or(phi1, phi2) => pp.intersperse(
                [
                    phi1.pretty(pp).nest(2).group(),
                    pp.text("∨"),
                    phi2.pretty(pp).nest(2).group(),
                ],
                pp.space(),
            ),
            _ => self.pretty_and(pp),
        }
    }

    fn pretty_and<'b, D, B>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, B>
    where
        D: pretty::DocAllocator<'b, B>,
        D::Doc: Clone,
        B: Clone,
    {
        match self {
            Formula::And(phi1, phi2) => pp.intersperse(
                [
                    phi1.pretty_and(pp).nest(2).group(),
                    pp.text("∧"),
                    phi2.pretty_and(pp).nest(2).group(),
                ],
                pp.space(),
            ),
            _ => self.pretty_not(pp),
        }
    }

    fn pretty_not<'b, D, B>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, B>
    where
        D: pretty::DocAllocator<'b, B>,
        D::Doc: Clone,
        B: Clone,
    {
        match self {
            Formula::Not(phi) => pp.text("¬").append(phi.pretty_atom(pp)),
            _ => self.pretty_atom(pp),
        }
    }

    fn pretty_atom<'b, D, B>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, B>
    where
        D: pretty::DocAllocator<'b, B>,
        D::Doc: Clone,
        B: Clone,
    {
        match self {
            Formula::Proposition(a) => pp.text(a.to_string()),
            Formula::True => pp.text("⊤"),
            Formula::False => pp.text("⊥"),
            _ => self.pretty(pp).group().parens(),
        }
    }
}

impl<T> From<T> for Formula<T> {
    fn from(t: T) -> Formula<T> {
        Formula::Proposition(t)
    }
}

impl<T> std::fmt::Display for Formula<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pp = pretty::BoxAllocator;
        let doc = self.pretty::<_, ()>(&pp);
        doc.1.render_fmt(crate::options::DEFAULT_WIDTH, f)
    }
}
