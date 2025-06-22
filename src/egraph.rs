use std::collections::{BTreeMap, BTreeSet};
use smallvec::SmallVec;
use crate::Function;

/// An e-class identifier.
pub type Id = usize;

/// An operator, and a list of e-class identifiers for arguments.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ENode<T> {
    pub op: T,
    pub args: SmallVec<[Id;2]>,
}

impl<T> ENode<T> {
    /// Create a new e-node from an operator and a list of e-class identifiers
    pub fn new<I: IntoIterator<Item=Id>>(op: T, args: I) -> Self {
        ENode { op, args: args.into_iter().collect() }
    }
}

impl<T: std::fmt::Debug> std::fmt::Display for ENode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.args.is_empty() {
            write!(f, "{:?}", self.op)?;
        } else {
            write!(f, "{:?}{:?}", self.op, self.args)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct EGraph<T> {
    /// A map from e-nodes to their e-class.
    ///
    /// This map acts as the source of truth, from which other members are derived.
    /// Whenever this map is modified, we should also update the derived indices.
    pub nodes: BTreeMap<ENode<T>, Id>,

    /// A reverse index from e-class to the e-nodes with the e-class as an argument.
    pub parents: BTreeMap<Id, BTreeSet<ENode<T>>>,
    /// A reverse index from e-class to the e-nodes that belong to (map to) the e-class.
    pub members: BTreeMap<Id, BTreeSet<ENode<T>>>,

    /// A list of pending merge requests.
    ///
    /// These merge requests will not be processed until `rebuild` is called.
    pub pending: Vec<(Id, Id)>,
}

impl<T> Default for EGraph<T> {
    fn default() -> Self {
        EGraph {
            nodes: Default::default(),
            members: Default::default(),
            parents: Default::default(),
            pending: Default::default(),
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Display for EGraph<T> {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (id, members) in self.members.iter() {
            let mut iter = members.iter();
            if let Some(first) = iter.next() {
                write!(f, "EClass #{}: -> [ {}", id, first)?;
                for e_node in iter {
                    write!(f, ", {}", e_node)?;
                }
                writeln!(f, " ]")?;
            }
        }
        Ok(())
    }
}

impl<T: Function + Ord + Clone + std::fmt::Debug> EGraph<T> {

    
    pub fn validate(&self) {
        // Confirm all e-class references exist.
        for (node, id) in self.nodes.iter() {
            assert!(self.members.get(id).unwrap().contains(node));
            for id in node.args.iter() {
                assert!(self.parents.get(id).unwrap().contains(node));
                assert!(self.members.contains_key(id));
            }
        }
        for (id, nodes) in self.members.iter() {
            for node in nodes.iter() {
                assert_eq!(self.nodes.get(node), Some(id));
            }
        }
    }

    /// Introduces the equivalence of two expressions.
    pub fn equate(&mut self, e0: Vec<T>, e1: Vec<T>) {
        let id0 = self.insert(e0);
        let id1 = self.insert(e1);
        self.merge(id0, id1);
    }

    /// Adds an expression to the e-graph.
    ///
    /// The `expr` argument is expected to be in pre-order.
    pub fn insert(&mut self, mut expr: Vec<T>) -> Id {
        // Repeatedly pop the tail of `expr` and the inserted `args`,
        // to find that e-node in `self.nodes` and push that e-class id.
        let mut ids = Vec::new();
        while let Some(op) = expr.pop() {
            let inputs = op.inputs();
            let args = ids[ids.len() - inputs..].iter().cloned().rev();
            let id = self.ensure(ENode::new(op, args));
            ids.truncate(ids.len() - inputs);
            ids.push(id);
        }

        ids.pop().unwrap()
    }

    /// Finds the e-class identifier of an e-node, if it exists.
    fn locate(&self, e_node: &ENode<T>) -> Option<Id> {
        self.nodes.get(e_node).copied()
    }

    /// Ensures that an e-node is present in the e-graph, and returns its e-class id.
    ///
    /// If the e-node is not initially present, it is added and a new e-class is set up.
    pub fn ensure(&mut self, e_node: ENode<T>) -> Id {
        if let Some(id) = self.nodes.get(&e_node) {
            *id
        }
        else {
            let new_id = self.new_id();
            // 1. Add e_node to parents of each element of `args`.
            for e_class in e_node.args.iter() {
                self.parents.entry(*e_class).or_default().insert(e_node.clone());
            }
            // 2. Form a new e-class with `e_node` as its only member.
            self.members.insert(new_id, BTreeSet::from([e_node.clone()]));
            // 3. Add `e_node` to `self.nodes`.
            self.nodes.insert(e_node, new_id);
            new_id
        }
    }

    /// Generate an e-class identifier that is not in use by the e-graph.
    fn new_id(&self) -> usize {
        self.members
            .last_key_value()
            .map(|(id, _)| id + 1)
            .unwrap_or(0)
    }

    /// Requests a merge of two e-classes.
    pub fn merge(&mut self, a: Id, b: Id) {
        if a != b {
            self.pending.push((a, b));
        }
    }

    /// Applies pending merges and restores invariants. Returns true if any merges occurred.
    pub fn refresh(&mut self) -> bool {
        
        // Record the initial number of e-classes.
        let prior_classes = self.members.len();

        // Continue for as long as there are pending merges.
        // Stopping early is not an option, as merges that are produced
        // must be resolved to restore the "congruence" invariant.
        while !self.pending.is_empty() {

            // 0. Plan merges between e-classes.
            let mut uf = BTreeMap::new();
            for (a, b) in self.pending.iter().copied() { uf.union(&a, &b); }
            // Groups of e-classes that will each be merged into one e-class.
            let mut new_classes = BTreeMap::new();
            for x in self.pending.drain(..).flat_map(|(a, b)| [a, b]) {
                let root = *uf.find(&x).unwrap();
                new_classes.entry(root).or_insert_with(BTreeSet::new).insert(x);
            }
            // Map for each merged e-class to its representative e-class identifier.
            // Choose the e-class with the most members and parents as the representative.
            let mut new_nodes = BTreeMap::new();
            for (_root, e_class) in new_classes.iter() {
                // Choose the new id to be the e-class with the most combined members and parents.
                // This minimizes the amount of work we'll have to do to refresh the stale e-nodes.
                let new_id = *e_class.iter().map(|id| (self.members.get(id).map(|m| m.len()).unwrap_or(0) + self.parents.get(id).map(|p| p.len()).unwrap_or(0), id)).min().unwrap().1;
                for id in e_class.iter().copied() {
                    new_nodes.insert(id, new_id);
                }
            }

            // 1. Remove any defunct e-classes, and enqueue their e-nodes for refresh.
            let mut refresh = BTreeSet::new();
            for (_root, class) in new_classes {
                for e_class in class {
                    if new_nodes[&e_class] != e_class {
                        if let Some(members) = self.members.remove(&e_class) {
                            refresh.extend(members);
                        }
                        if let Some(parents) = self.parents.remove(&e_class) {
                            refresh.extend(parents);
                        }
                    }
                }
            }

            // 2. Refresh each stale e-node.
            for mut e_node in refresh {
                let mut id = self.remove(&e_node).unwrap();
                // Update the e-classes referenced by the e-node.
                if let Some(new) = new_nodes.get(&id) {
                    id = *new;
                }
                for arg in e_node.args.iter_mut() {
                    if let Some(id) = new_nodes.get(arg) {
                        *arg = *id;
                    }
                }

                // Introduce evidence of the refreshed e-node.
                // The e-node may already exist, associated with another class;
                // In that case, enqueue a merge but do not touch anything else.
                if self.nodes.get(&e_node).map(|i| *i == id) == Some(false) {
                    let mut other_id = *self.nodes.get(&e_node).unwrap();
                    if let Some(newer) = new_nodes.get(&other_id) { other_id = *newer; }
                    self.pending.push((other_id, id));
                }
                else {
                    // Introduce evidence of the refreshed e-node.
                    self.members.entry(id).or_default().insert(e_node.clone());
                    for arg in e_node.args.iter() {
                        self.parents.entry(*arg).or_default().insert(e_node.clone());
                    }

                    self.nodes.insert(e_node, id);
                }
            }

        }

        self.members.len() < prior_classes
    }

    /// Removes an e-node from the e-graph, and returns its e-class identifier.
    ///
    /// This method can be called even when the e-graph is in an inconsistent state,
    /// as it only removes evidence of the e-node, even if some of that evidence is missing.
    fn remove(&mut self, e_node: &ENode<T>) -> Option<Id> {
        for arg in e_node.args.iter() {
            if let Some(parents) = self.parents.get_mut(arg) {
                parents.remove(e_node);
            }
        }
        // Extract the stale e-node and its e-class.
        if let Some(id) = self.nodes.remove(e_node) {
            // Remove evidence of the stale e-node.
            if let Some(members) = self.members.get_mut(&id) {
                members.remove(e_node);
            }
            Some(id)
        }
        else { None }
    }
}

trait UnionFind<T> {
    /// Sets `self[x]` to the root from `x`, and returns a reference to the root.
    fn find<'a>(&'a mut self, x: &T) -> Option<&'a T>;
    /// Ensures that `x` and `y` have the same root.
    fn union(&mut self, x: &T, y: &T);
}

impl<T: Clone + Ord> UnionFind<T> for BTreeMap<T, T> {
    fn find<'a>(&'a mut self, x: &T) -> Option<&'a T> {
        if !self.contains_key(x) {
            None
        } else {
            if self[x] != self[&self[x]] {
                // Path halving
                let mut y = self[x].clone();
                while y != self[&y] {
                    let grandparent = self[&self[&y]].clone();
                    *self.get_mut(&y).unwrap() = grandparent;
                    y.clone_from(&self[&y]);
                }
                *self.get_mut(x).unwrap() = y;
            }
            Some(&self[x])
        }
    }

    fn union(&mut self, x: &T, y: &T) {
        match (self.find(x).is_some(), self.find(y).is_some()) {
            (true, true) => {
                if self[x] != self[y] {
                    let root_x = self[x].clone();
                    let root_y = self[y].clone();
                    self.insert(root_x, root_y);
                }
            }
            (false, true) => {
                self.insert(x.clone(), self[y].clone());
            }
            (true, false) => {
                self.insert(y.clone(), self[x].clone());
            }
            (false, false) => {
                self.insert(x.clone(), x.clone());
                self.insert(y.clone(), x.clone());
            }
        }
    }
}

/// A type that can inspect an e-graph and suggest merges.
pub trait Searcher<T> {
    /// From an e-graph, enumerate all merge actions to take.
    fn search(&self, e_graph: &EGraph<T>) -> Vec<(ENode<T>, ENode<T>)>;
}

pub mod patterns {

    use crate::egraph::{EGraph, ENode, Id};
    use crate::Function;

    /// Pattern matching looks a lot like motif search in graphs.
    ///
    /// The pattern defines a subgraph shape with labeled nodes and edges.
    /// E.g. the pattern `(+ x 0)` matches any two eclasses, where
    ///   1. The first eclass (+) contains an e-node with the operator `+` and two arguments,
    ///   2. The second eclass (x) contains an e-node.
    ///   3. The first e-node is connected to the e-class of the second e-node by a 0-edge.
    ///   4. The first e-node is connected to the e-class of the 0 e-node by a 1-edge.
    ///
    /// Search is similarly interesting. We could start at the `0` e-node, and search backwards.
    /// Any `+` e-node that is connected to the `0` e-node by a 1-edge is a match.
    /// We might end up needing to do treefrog leapjoin style intersections!

    #[derive(Clone, Debug)]
    pub enum Symbol<T> {
        Operator(T),     // Operator that must match exactly.
        Variable(usize), // Variable that must bind to an e-class.
    }

    #[derive(Clone, Debug)]
    pub struct Pattern<T> {
        pattern: Vec<Symbol<T>>,
        span: Vec<usize>,      // length of term at each index.
        var_bound: Vec<usize>, // max variable index of each span, plus one.
    }

    /// A tree of bindings, where nodes at each depth bind that variable to an e-class.
    #[derive(Clone, Debug)]
    pub struct Binding {
        pub class: Id,
        pub nexts: Vec<Binding>,
    }

    impl<T: Function> Pattern<T> {
        /// Construct a new pattern from a list of search symbols.
        ///
        /// The symbols are a pre-order expression that may additionally contain variables.
        /// The re-use of variable terms indicates that the same e-class must be found.
        pub fn new(pattern: Vec<Symbol<T>>) -> Self {
            let mut span = Vec::new();
            let mut var_bound = Vec::new();
            // We could build these bottom-up in linear time, but this is easier for me.
            for index in 0..pattern.len() {
                let length = Self::span(&pattern[index..]);
                let max_var = Self::max_var(&pattern[index..][..length]);
                span.push(length);
                var_bound.push(max_var);
            }
            Pattern { pattern, span, var_bound, }
        }

        fn max_var(slice: &[Symbol<T>]) -> usize {
            slice
                .iter()
                .flat_map(|sym| match sym {
                    Symbol::Operator(_) => None,
                    Symbol::Variable(v) => Some(*v + 1),
                })
                .max()
                .unwrap_or(0)
        }

        /// The number of symbols in the pattern.
        fn span(pattern: &[Symbol<T>]) -> usize {
            let mut defecit = 1;
            for (index, symbol) in pattern.iter().enumerate() {
                if let Symbol::Operator(op) = symbol {
                    defecit += op.inputs();
                }
                defecit -= 1;
                if defecit == 0 {
                    return index + 1;
                }
            }
            panic!("Incomplete pattern!");
        }
    }

    impl<T: Clone + Ord + Function + std::fmt::Debug> Pattern<T> {
        /// Given a pattern produce a list of valid variable bindings.
        ///
        /// The algorithm binds variables in order, and looks for potential invalidations.
        /// The invalidations result from a subterm not being found in the e-graph.
        /// There are better algorithms that follow worst-case optimal joins, and other
        /// graph motif search techniques.
        ///
        /// Careful consideration of variable ordering can reduce the visited search space.
        pub fn bind(self: &Pattern<T>, e_graph: &EGraph<T>) -> Vec<Vec<Id>> {
            let mut results = vec![vec![]];
            if self.var_bound[0] == 0 {
                if self.find(e_graph, &[]).is_some() {
                    return vec![vec![]];
                } else {
                    return vec![];
                }
            }

            for _ in 0 .. self.var_bound[0] {
                let mut next_results = Vec::new();
                for mut context in std::mem::take(&mut results) {
                    // Variables `0 .. context.len()` are already bound.
                    // We want to consider the possible bindings to the next variable.
                    // Any binding that produces a sub-e-node that is not present is not a match.
                    // Each iteration we'll push an e-class id onto to `context`, and pop it at the end.
                    for (id, _e_class) in e_graph.members.iter() {
                        context.push(*id);

                        // Seek any grounded subterms and see if they match in the e-graph.
                        let mut fail = false;
                        let mut finger = 0;
                        while finger < self.pattern.len() {
                            let span = self.span[finger];
                            match self.var_bound[finger].cmp(&context.len()) {
                                std::cmp::Ordering::Less => {
                                    // The whole span cannot be invalidated by context,
                                    // because all prior variables have been validated.
                                    finger += span;
                                },
                                std::cmp::Ordering::Equal => {
                                    // The span could be newly invalidated by context.
                                    let slice = &self.pattern[finger..][..span];
                                    if Self::seek(e_graph, slice, &context).is_none() {
                                        fail = true;
                                        break;
                                    }
                                    finger += span;
                                },
                                std::cmp::Ordering::Greater => {
                                    // A subspan could yet be invalidated by context.
                                    finger += 1;
                                },
                            }
                        }
                        if !fail {
                            next_results.push(context.clone());
                        }

                        context.pop();
                    }
                }
                results = next_results;
            }
            results
        }

        /// Find the e-classes the expression in pre-order belongs to, if it exists.
        ///
        /// All variables in `pattern` must be bound in `context`.
        fn seek(e_graph: &EGraph<T>, pattern: &[Symbol<T>], context: &[Id]) -> Option<Id> {
            // Repeatedly pop the tail of `expr` and the inserted `args`,
            // to find that e-node in `self.nodes` and push that e-class id.
            let mut ids = Vec::new();
            for sym in pattern.iter().rev() {
                match sym {
                    Symbol::Operator(op) => {
                        let inputs = op.inputs();
                        let args = &ids[ids.len() - inputs..];
                        let e_node = ENode::new(op.clone(), args.iter().cloned().rev());
                        ids.truncate(ids.len() - inputs);
                        ids.push(e_graph.locate(&e_node)?);
                    }
                    Symbol::Variable(var) => {
                        ids.push(context[*var]);
                    }
                }
            }
            Some(ids.pop().unwrap())
        }

        /// Attempts to locate the pattern with context in the e-graph.
        pub fn find(&self, e_graph: &EGraph<T>, context: &[Id]) -> Option<Id> {
            Self::seek(e_graph, &self.pattern, context)
        }

        pub fn mint(&self, e_graph: &mut EGraph<T>, context: &[Id]) -> Id {
            // Repeatedly pop the tail of `expr` and the inserted `args`,
            // to find that e-node in `self.nodes` and push that e-class id.
            let mut ids = Vec::new();
            for sym in self.pattern.iter().rev() {
                match sym {
                    Symbol::Operator(op) => {
                        let inputs = op.inputs();
                        let args = &ids[ids.len() - inputs..];
                        let e_node = ENode::new(op.clone(), args.iter().cloned().rev());
                        ids.truncate(ids.len() - inputs);
                        ids.push(e_graph.ensure(e_node));
                    }
                    Symbol::Variable(var) => {
                        ids.push(context[*var]);
                    }
                }
            }
            ids.pop().unwrap()
        }
    }

    #[derive(Clone, Debug)]
    pub struct Rewrite<T> {
        pub source: Pattern<T>,
        pub target: Pattern<T>,
    }

    impl<T: Clone + Function + Ord + std::fmt::Debug> Rewrite<T> {
        pub fn apply(&self, e_graph: &mut EGraph<T>) {
            let binds = self.source.bind(e_graph);
            for bind in binds {
                let source = self.source.find(e_graph, &bind).unwrap();
                let target = self.target.mint(e_graph, &bind);
                e_graph.merge(source, target);
            }
        }
    }
}