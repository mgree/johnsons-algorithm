// https://www.cs.tufts.edu/comp/150GA/homeworks/hw1/Johnson%2075.PDF
// finding all elementary circuits in a graph

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;

pub type V = usize;
pub type Cycle = Vec<V>;
// invariant: every vertex should have an entry, even if its empty
pub type Graph = BTreeMap<V, HashSet<V>>;

use crate::checker::Checker;
use crate::syntax::{Atom, Constraint, Literal, Program};

impl Program {
    /// Given a logic program P (`self`) and a loop (`cycle`), returns the literals G_ij and atoms
    pub fn loop_formula(&self, checker: &Checker, cycle: &[V]) -> (Vec<Literal>, Vec<Atom>) {
        let mut neg = Vec::new();

        for constraint in self.0.iter() {
            match constraint {
                Constraint::Rule(head, ls) => {
                    if cycle.contains(&checker.atom_number(head)) {
                        if ls
                            .iter()
                            .filter(|l| l.is_positive())
                            .map(|l| checker.atom_number(l.as_atom()))
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

        let mut cycle: Vec<_> = cycle.iter().map(|i| checker.atoms[*i].clone()).collect();
        assert_eq!(cycle[0], cycle[cycle.len() - 1]);
        cycle.pop();

        (neg, cycle)
    }

    /// Computes R^+ and R^- from Lin and Zhao (AI 2004).
    pub fn loop_partition(&self, checker: &Checker, cycle: &[V]) -> (Program, Program) {
        let mut pos = Program(Vec::new());
        let mut neg = Program(Vec::new());

        for constraint in self.0.iter() {
            match constraint {
                Constraint::Rule(head, ls) => {
                    if cycle.contains(&checker.atom_number(head)) {
                        if ls
                            .iter()
                            .filter(|l| l.is_positive())
                            .map(|l| checker.atom_number(l.as_atom()))
                            .any(|a| cycle.contains(&a))
                        {
                            pos.0.push(constraint.clone());
                        } else {
                            neg.0.push(constraint.clone());
                        }
                    }
                }
                Constraint::Fact(head) => {
                    if cycle.contains(&checker.atom_number(head)) {
                        neg.0.push(constraint.clone());
                    }
                }
                Constraint::Integrity(..) => (),
            }
        }

        (pos, neg)
    }
}

#[cfg(test)]
mod test_partition {
    use super::*;

    #[test]
    fn lin_zhao_eg_text_p119() {
        let p = Program::parse("a :- b. b :- a. a.").expect("valid parse");
        let checker = Checker::new(&p).expect("valid program");

        let graph = checker
            .backrefs
            .iter()
            .enumerate()
            .map(|(h, ls)| (h, ls.clone()))
            .collect();
        let circuits = find(&graph);
        assert_eq!(circuits.len(), 1);

        let (pos, neg) = p.loop_partition(&checker, &circuits[0]);

        assert_eq!(pos.0.len(), 2);
        if pos.0[0] != p.0[0] {
            assert_eq!(pos.0[0], p.0[1]);
            assert_eq!(pos.0[1], p.0[0]);
        } else {
            assert_eq!(pos.0[1], p.0[1]);
        }
        assert_eq!(neg.0.len(), 1);
        assert_eq!(neg.0[0], p.0[2]);
    }

    #[test]
    fn lin_zhao_eg1_p120() {
        let p = Program::parse(concat!(
            "a :- b. b :- a. a :- not c.\n",
            "c :- d. d :- c. c :- not a."
        ))
        .expect("valid parse");
        let checker = Checker::new(&p).expect("valid program");

        let graph = checker
            .backrefs
            .iter()
            .enumerate()
            .map(|(h, ls)| (h, ls.clone()))
            .collect();
        let circuits = find(&graph);
        assert_eq!(circuits.len(), 2);

        // the asserts below are very much order dependent!!!

        // circuit 0
        let (pos, neg) = p.loop_partition(&checker, &circuits[0]);

        assert_eq!(pos.0.len(), 2);
        assert_eq!(pos.0[0], p.0[0]);
        assert_eq!(pos.0[1], p.0[1]);
        assert_eq!(neg.0.len(), 1);
        assert_eq!(neg.0[0], p.0[2]);

        // circuit 1
        let (pos, neg) = p.loop_partition(&checker, &circuits[1]);

        assert_eq!(pos.0.len(), 2);
        assert_eq!(pos.0[0], p.0[3]);
        assert_eq!(pos.0[1], p.0[4]);
        assert_eq!(neg.0.len(), 1);
        assert_eq!(neg.0[0], p.0[5]);
    }

    #[test]
    fn lin_zhao_eg2_p120() {
        let p = Program::parse(concat!(
            "a :- b. b :- a. a :- not c.\n",
            "c :- d. d :- c. c :- not a."
        ))
        .expect("valid parse");
        let checker = Checker::new(&p).expect("valid program");

        let graph = checker
            .backrefs
            .iter()
            .enumerate()
            .map(|(h, ls)| (h, ls.clone()))
            .collect();
        let circuits = find(&graph);
        assert_eq!(circuits.len(), 2);

        // the asserts below are very much order dependent!!!

        // circuit 0
        let (premises, conclusion) = p.loop_formula(&checker, &circuits[0]);
        assert_eq!(premises.len(), 1);
        assert_eq!(premises[0], Literal::Not(Atom::from("c", &[])));

        assert_eq!(conclusion.len(), 2);
        assert_eq!(
            conclusion,
            vec![Atom::from("a", &[]), Atom::from("b", &[]),]
        );

        // circuit 1
        let (premises, conclusion) = p.loop_formula(&checker, &circuits[1]);
        assert_eq!(premises.len(), 1);
        assert_eq!(premises[0], Literal::Not(Atom::from("a", &[])));

        assert_eq!(conclusion.len(), 2);
        assert_eq!(
            conclusion,
            vec![Atom::from("c", &[]), Atom::from("d", &[]),]
        );
    }
}

struct JohnsonsAlgorithm {
    b: HashMap<V, Vec<V>>,
    blocked: HashSet<V>,
    stack: Vec<V>,
    found: Vec<Cycle>,
}

pub fn find(graph: &Graph) -> Vec<Cycle> {
    let b = HashMap::from_iter(graph.keys().map(|v| (*v, Vec::new())));
    let blocked = HashSet::new();
    let stack = Vec::with_capacity(1 + (3 * graph.len()) / 4);
    let found = Vec::new();
    let mut ja = JohnsonsAlgorithm {
        b,
        blocked,
        stack,
        found,
    };

    ja.find_cycles(graph);

    ja.found
}

impl JohnsonsAlgorithm {
    fn unblock(&mut self, u: V) {
        self.blocked.remove(&u);

        while !self.b[&u].is_empty() {
            let w = self
                .b
                .get_mut(&u)
                .expect("valid blist entry")
                .pop()
                .expect("non-empty");
            if self.blocked.contains(&w) {
                self.unblock(w)
            }
        }
    }
    fn circuit(&mut self, ak: &Graph, v: V, s: V) -> bool {
        let mut found_circuit = false;

        self.stack.push(v);
        self.blocked.insert(v);

        // L1
        if let Some(ws) = ak.get(&v) {
            for w in ws {
                if *w == s {
                    // found a circuit!
                    let mut cycle = self.stack.clone();
                    cycle.push(s);
                    self.found.push(cycle);
                    found_circuit = true;
                } else if !self.blocked.contains(w) && self.circuit(ak, *w, s) {
                    found_circuit = true;
                }
            }
        }

        // L2
        if found_circuit {
            self.unblock(v);
        } else if let Some(ws) = ak.get(&v) {
            for w in ws {
                if !self.b[w].contains(&v) {
                    self.b.get_mut(w).expect("valid blist entry").push(v);
                }
            }
        }
        self.stack.pop();

        found_circuit
    }

    fn find_cycles(&mut self, graph: &Graph) {
        let mut s = 0;

        loop {
            // A_K is the strong component K with least vertex in {s, ...}

            // restrict graph
            // TODO: winnow iteratively?
            let ak = subgraph_from(graph, s);

            // compute SCC
            let scc = match strongly_connected_components(&ak)
                .into_iter()
                .filter(|scc| scc.len() > 1)
                .min_by_key(|scc| scc.len())
            {
                None => break,
                Some(scc) => scc,
            };

            // A_K is non_empty!

            // s is least vertex in vertices of A_K
            let mut ak_vertices = scc.iter();
            s = *ak_vertices.next().expect("non-empty subgraph");

            // clear blocked, B(i) for each i in V_K
            self.blocked.remove(&s);
            self.b.get_mut(&s).expect("valid blist entry").clear();

            for i in ak_vertices {
                self.blocked.remove(i);
                self.b.get_mut(i).expect("valid blist entry").clear();
            }

            // L3
            self.circuit(&ak, s, s);
            s += 1;
        }
    }
}

fn subgraph_from(graph: &Graph, s: V) -> Graph {
    graph
        .iter()
        .filter_map(|(v, ws)| {
            if v >= &s {
                Some((*v, ws.iter().filter(|w| *w >= &s).copied().collect()))
            } else {
                None
            }
        })
        .collect()
}

#[cfg(test)]
mod test_johnsons {
    use super::*;

    fn has_cycle(cycles: &[Cycle], mut c: Cycle) {
        let mut rotations = HashSet::new();

        assert!(!c.is_empty());

        loop {
            if rotations.contains(&c) {
                break;
            }

            // save current rotation
            rotations.insert(c.clone());

            // beginning and ending should be the same

            c.pop(); // drop the end
            c.rotate_right(1); // rotate
            c.push(c[0]); // put a new end on
        }

        assert_eq!(cycles.iter().filter(|c| rotations.contains(*c)).count(), 1);
    }

    // tests cribbed from Benedikt Linse's impl at https://github.com/1123/johnson
    // under Apache 2.0 license

    #[test]
    fn two_binary_cycles() {
        let mut g = BTreeMap::new();

        g.insert(1, HashSet::from([3]));
        g.insert(3, HashSet::from([1, 2]));
        g.insert(2, HashSet::from([3]));

        let cycles = find(&g);
        assert_eq!(cycles.len(), 2);

        has_cycle(&cycles, vec![3, 1, 3]); // deliberately using the wrong order to exercise has_cycle
        has_cycle(&cycles, vec![2, 3, 2]);
    }

    #[test]
    fn one_binary_one_ternary_cycle() {
        let mut g = BTreeMap::new();

        g.insert(1, HashSet::from([2]));
        g.insert(2, HashSet::from([1, 3]));
        g.insert(3, HashSet::new());
        g.insert(4, HashSet::from([5]));
        g.insert(5, HashSet::from([6]));
        g.insert(6, HashSet::from([4]));

        let cycles = find(&g);
        assert_eq!(cycles.len(), 2);

        has_cycle(&cycles, vec![1, 2, 1]);
        has_cycle(&cycles, vec![4, 5, 6, 4]);
    }

    #[test]
    fn one_binary_cycle() {
        let g = BTreeMap::from([
            (1, HashSet::from([2])),
            (2, HashSet::from([1])),
            (3, HashSet::from([1, 2])),
        ]);

        let cycles = find(&g);
        assert_eq!(cycles.len(), 1);

        has_cycle(&cycles, vec![1, 2, 1]);
    }

    #[test]
    fn two_overlapping_cycles() {
        let g = BTreeMap::from([
            (1, HashSet::from([3])),
            (2, HashSet::from([1])),
            (3, HashSet::from([1, 2])),
        ]);

        let cycles = find(&g);
        eprintln!("{:?}", cycles);
        assert_eq!(cycles.len(), 2);

        has_cycle(&cycles, vec![1, 3, 1]);
        has_cycle(&cycles, vec![2, 1, 3, 2]); // deliberate rotation
    }

    #[test]
    fn subgraph() {
        let g = BTreeMap::from([
            (1, HashSet::from([3])),
            (3, HashSet::from([1, 2])),
            (2, HashSet::from([3])),
        ]);

        let sub = subgraph_from(&g, 2);
        assert!(!sub.contains_key(&1));
        assert!(sub.contains_key(&2));
        assert!(sub.contains_key(&3));

        assert_eq!(sub.get(&2).expect("edges"), &HashSet::from([3]));
        assert_eq!(sub.get(&3).expect("edges"), &HashSet::from([2]));
    }
}

struct TarjansAlgorithm {
    index: usize,
    index_of: HashMap<V, usize>,
    lowlink_of: HashMap<V, usize>,
    stack: Vec<V>,
    components: Vec<BTreeSet<V>>,
}

fn strongly_connected_components(graph: &Graph) -> Vec<BTreeSet<V>> {
    let index = 0;
    let index_of = HashMap::new();
    let lowlink_of = HashMap::from_iter(graph.keys().map(|v| (*v, 0)));
    let stack = Vec::new();
    let components = Vec::new();
    let mut ta = TarjansAlgorithm {
        index,
        index_of,
        lowlink_of,
        stack,
        components,
    };

    for v in graph.keys() {
        if ta.index_of.get(v).is_none() {
            ta.strong_connect(graph, v);
        }
    }

    ta.components
}

impl TarjansAlgorithm {
    fn strong_connect(&mut self, graph: &Graph, v: &V) {
        self.index_of.insert(*v, self.index);
        self.lowlink_of.insert(*v, self.index);
        self.index += 1;

        self.stack.push(*v);

        // look at each of v's outgoing edges
        if let Some(ws) = graph.get(v) {
            for w in ws {
                if self.index_of.get(w).is_none() {
                    // first visit of w
                    self.strong_connect(graph, w);
                    self.lowlink_of
                        .insert(*v, std::cmp::min(self.lowlink_of[v], self.lowlink_of[w]));
                } else if self.stack.contains(w) {
                    // w is on the stack, so it's in the same SCC
                    // NB we're deliberately using w's index, not its lowlink
                    self.lowlink_of
                        .insert(*v, std::cmp::min(self.lowlink_of[v], self.index_of[w]));
                }
                // if both these fail, then w is in some other SCC
            }
        }
        if self.lowlink_of[v] == self.index_of[v] {
            // v is a root node! we've found an SCC
            let mut scc = BTreeSet::new();

            while let Some(w) = self.stack.pop() {
                scc.insert(w);

                if w == *v {
                    break;
                }
            }

            // it's only an SCC
            if scc.len() > 1 {
                self.components.push(scc);
            }
        }
    }
}

#[cfg(test)]
mod test_tarjans {
    use super::*;

    // tests cribbed from Benedikt Linse's impl at https://github.com/1123/johnson
    // under Apache 2.0 license

    #[test]
    fn two_node_circuit() {
        let mut g = BTreeMap::new();

        let v0 = 0;
        let v1 = 1;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::from([v0]));

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], BTreeSet::from([v0, v1]));
    }

    #[test]
    fn single_node_no_sccs() {
        let mut g = BTreeMap::new();

        let v0 = 0;
        let v1 = 1;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::new());

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 0);
    }

    #[test]
    fn single_node_no_sccs_funny_numbering() {
        let mut g = BTreeMap::new();

        let v0 = 50;
        let v1 = 3;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::new());

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 0);
    }

    #[test]
    fn four_node_cycle() {
        let mut g = BTreeMap::new();

        let v0 = 5;
        let v1 = 6;
        let v2 = 7;
        let v3 = 8;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::from([v2]));
        g.insert(v2, HashSet::from([v3]));
        g.insert(v3, HashSet::from([v0]));

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], BTreeSet::from([v0, v1, v2, v3]));
    }

    #[test]
    fn two_separate_components() {
        let mut g = BTreeMap::new();

        let v0 = 5;
        let v1 = 6;
        let v2 = 7;
        let v3 = 8;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::from([v0]));
        g.insert(v2, HashSet::from([v3]));
        g.insert(v3, HashSet::from([v2]));

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 2);
        // we know we'll get this ordering because graphs are btrees, and we start with the lowest vertex
        assert_eq!(sccs[0], BTreeSet::from([v0, v1]));
        assert_eq!(sccs[1], BTreeSet::from([v2, v3]));
    }

    #[test]
    fn two_separate_components_weakly_linked() {
        let mut g = BTreeMap::new();

        let v0 = 5;
        let v1 = 6;
        let v2 = 7;
        let v3 = 8;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::from([v0, v2]));
        g.insert(v2, HashSet::from([v3]));
        g.insert(v3, HashSet::from([v2]));

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 2);

        // harder to know which SCC will be first, best to allow either order
        if sccs[0] == BTreeSet::from([v0, v1]) {
            assert_eq!(sccs[1], BTreeSet::from([v2, v3]));
        } else {
            assert_eq!(sccs[0], BTreeSet::from([v2, v3]));
            assert_eq!(sccs[1], BTreeSet::from([v0, v1]));
        }
    }

    #[test]
    fn one_component_extra_node() {
        let mut g = BTreeMap::new();

        let v0 = 1;
        let v1 = 2;
        let v2 = 3;
        let v3 = 4;

        g.insert(v0, HashSet::from([v1]));
        g.insert(v1, HashSet::from([v2, v3]));
        g.insert(v2, HashSet::from([v1, v3]));
        g.insert(v3, HashSet::from([v2]));

        let sccs = strongly_connected_components(&g);

        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], BTreeSet::from([v1, v2, v3]));
    }
}
