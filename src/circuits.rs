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

struct JohnsonsAlgorithm {
    b: Vec<Vec<V>>, // should this be HashMap<V, HashSet<V>> ?
    blocked: HashSet<V>,
    stack: Vec<V>,
    found: Vec<Cycle>,
}

pub fn find(graph: &Graph) -> Vec<Cycle> {
    let n = graph.keys().last().expect("non-empty graph");
    let b = vec![Vec::new(); *n];
    let blocked = HashSet::new();
    let stack = Vec::with_capacity((3 * n) / 4);
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

        while !self.b[u].is_empty() {
            let w = self.b[u].pop().expect("non-empty");
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
                if !self.b[*w].contains(&v) {
                    self.b[*w].push(v);
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
            let ak = self.subgraph_from(graph, s); // TODO compute strong components using Tarjan's alg

            let scc = match strongly_connected_components(&ak)
                .into_iter()
                .filter(|scc| scc.len() > 1)
                .min_by_key(|scc| scc.len())
            {
                None => break,
                Some(scc) => scc,
            };

            // A_K is non_empty

            // s is least vertex in vertices of A_K
            let mut ak_vertices = scc.iter();
            s = *ak_vertices.next().expect("non-empty subgraph");

            // clear blocked, B(i) for each i in V_K
            self.blocked.remove(&s);
            self.b[s].clear();

            for i in ak_vertices {
                self.blocked.remove(i);
                self.b[*i].clear();
            }

            // L3
            self.circuit(&ak, s, s);
            s += 1;
        }
    }

    fn subgraph_from(&self, graph: &Graph, s: V) -> Graph {
        todo!()
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
mod test {
    use super::*;

    // test cribbed from Benedikt Line's impl at https://github.com/1123/johnson
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
