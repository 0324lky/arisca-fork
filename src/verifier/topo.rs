use crate::bipoly::VarId;

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

pub trait VarDomain {
    fn candidates(&self) -> &[VarId];
    fn update(&mut self, target: VarId);
    fn len(&self) -> usize;
}

#[derive(Clone)]
pub struct TopoVar {
    adj: Arc<HashMap<VarId, Vec<VarId>>>,
    in_degree: HashMap<VarId, usize>,
    queue: Vec<VarId>,
    /// While a checkpoint is active: each in-degree `update` lowered, with its earlier value.
    log: Option<Vec<(VarId, usize)>>,
}

impl TopoVar {
    pub fn new(adj: HashMap<VarId, Vec<VarId>>) -> Self {
        let mut in_degree = HashMap::new();
        for (v, adj) in &adj {
            in_degree.entry(*v).or_insert(0);
            for u in adj {
                *in_degree.entry(*u).or_insert(0) += 1;
            }
        }
        let queue = in_degree
            .iter()
            .filter_map(|(v, &in_degree)| if in_degree == 0 { Some(*v) } else { None })
            .collect();
        TopoVar {
            adj: Arc::new(adj),
            in_degree,
            queue,
            log: None,
        }
    }

    /// Starts recording in-degree changes; returns the ready queue to restore with.
    fn checkpoint(&mut self) -> Vec<VarId> {
        self.log = Some(Vec::new());
        self.queue.clone()
    }

    /// Returns to the checkpoint, given its ready queue; recording goes on from there.
    fn rollback(&mut self, queue: &[VarId]) {
        if let Some(log) = &mut self.log {
            for (v, degree) in log.drain(..).rev() {
                *self
                    .in_degree
                    .get_mut(&v)
                    .expect("a logged vertex has an in-degree") = degree;
            }
        }
        self.queue.clear();
        self.queue.extend_from_slice(queue);
    }

    pub fn bfs(&self) -> Vec<VarId> {
        let mut current_in_degree = self.in_degree.clone();

        let mut queue: VecDeque<VarId> = self.queue.clone().into();
        let mut result = Vec::new();

        while let Some(u) = queue.pop_front() {
            result.push(u.clone());

            if let Some(neighbors) = self.adj.get(&u) {
                for v in neighbors {
                    if let Some(degree) = current_in_degree.get_mut(v) {
                        *degree -= 1;
                        if *degree == 0 {
                            queue.push_back(v.clone());
                        }
                    }
                }
            }
        }
        result.reverse();
        result
    }

    pub fn dfs(&self) -> Vec<VarId> {
        let mut visited: HashSet<VarId> = HashSet::new();
        let mut result = Vec::new();

        for node in self.queue.iter() {
            if !visited.contains(node) {
                self.dfs_visit(node.clone(), &mut visited, &mut result);
            }
        }

        result
    }

    fn dfs_visit(&self, u: VarId, visited: &mut HashSet<VarId>, result: &mut Vec<VarId>) {
        visited.insert(u.clone());

        if let Some(neighbors) = self.adj.get(&u) {
            for v in neighbors {
                if !visited.contains(v) {
                    self.dfs_visit(v.clone(), visited, result);
                }
            }
        }
        result.push(u);
    }
}

impl VarDomain for TopoVar {
    fn candidates(&self) -> &[VarId] {
        &self.queue
    }

    fn update(&mut self, target: VarId) {
        if let Some(pos) = self.queue.iter().position(|&x| x == target) {
            self.queue.swap_remove(pos);
        }
        if let Some(neighbors) = self.adj.get(&target) {
            for neighbor in neighbors {
                if let Some(deg) = self.in_degree.get_mut(neighbor) {
                    if let Some(log) = &mut self.log {
                        log.push((*neighbor, *deg));
                    }
                    *deg -= 1;
                    if *deg == 0 {
                        self.queue.push(*neighbor);
                    }
                }
            }
        }
    }

    fn len(&self) -> usize {
        self.in_degree.len()
    }
}

#[derive(Clone)]
pub struct VecVar {
    candidates: Vec<VarId>,
    len: usize,
}

impl VecVar {
    pub fn new(candidates: Vec<VarId>) -> Self {
        VecVar {
            len: candidates.len(),
            candidates,
        }
    }
}

impl VarDomain for VecVar {
    fn candidates(&self) -> &[VarId] {
        &self.candidates[self.candidates.len().saturating_sub(1)..]
    }

    fn update(&mut self, _target: VarId) {
        self.candidates.pop();
    }

    fn len(&self) -> usize {
        self.len
    }
}

#[derive(Clone)]
pub enum Domain {
    Topo(TopoVar),
    Vec(VecVar),
}

/// A candidate domain at a point it can return to (see [`Domain::checkpoint`]).
pub enum DomainCheckpoint {
    /// A topological domain logs its in-degree changes; the checkpoint keeps its ready queue.
    Topo(Vec<VarId>),
    /// Any other domain is copied.
    Copy(Domain),
}

impl Domain {
    /// Marks the current state for [`restore`](Self::restore) without copying a topological
    /// domain's in-degree map (one entry per node).
    pub fn checkpoint(&mut self) -> DomainCheckpoint {
        match self {
            Domain::Topo(topo) => DomainCheckpoint::Topo(topo.checkpoint()),
            other => DomainCheckpoint::Copy(other.clone()),
        }
    }

    pub fn restore(&mut self, checkpoint: &DomainCheckpoint) {
        match (self, checkpoint) {
            (Domain::Topo(topo), DomainCheckpoint::Topo(queue)) => topo.rollback(queue),
            (domain, DomainCheckpoint::Copy(copy)) => *domain = copy.clone(),
            _ => unreachable!("a checkpoint of another kind of domain"),
        }
    }

    /// Keeps the current state and stops recording.
    pub fn clear_checkpoint(&mut self) {
        if let Domain::Topo(topo) = self {
            topo.log = None;
        }
    }
}

impl VarDomain for Domain {
    fn candidates(&self) -> &[VarId] {
        match self {
            Domain::Topo(topo) => topo.candidates(),
            Domain::Vec(vec) => vec.candidates(),
        }
    }

    fn update(&mut self, target: VarId) {
        match self {
            Domain::Topo(topo) => topo.update(target),
            Domain::Vec(vec) => vec.update(target),
        }
    }

    fn len(&self) -> usize {
        match self {
            Domain::Topo(topo) => topo.len(),
            Domain::Vec(vec) => vec.len(),
        }
    }
}
