mod debug;
mod ops;
mod term;

use rug::Integer;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet, btree_map::Entry};
pub use term::{Term, VarId};

/// A change recorded since the last checkpoint (see [`Polynomial::checkpoint`]).
enum Change {
    /// A term's value before the change (`None`: the term was absent).
    Term(Term, Option<Integer>),
    /// The whole map before it was replaced at once.
    Whole(BTreeMap<Term, Integer>),
}

#[derive(Default)]
pub struct Polynomial {
    pub terms: BTreeMap<Term, Integer>,
    /// The changes since the last checkpoint, while recording. A recording polynomial must be
    /// changed through its methods, not through `terms`, or a rollback cannot restore it.
    log: Option<Vec<Change>>,
}

impl Clone for Polynomial {
    /// A copy carries the terms only: recording belongs to the original.
    fn clone(&self) -> Self {
        Self {
            terms: self.terms.clone(),
            log: None,
        }
    }
}

impl Polynomial {
    pub fn new() -> Self {
        Self::default()
    }

    /// Starts recording changes, so that [`rollback`](Self::rollback) can return to the
    /// polynomial as it is now.
    pub fn checkpoint(&mut self) {
        self.log = Some(Vec::new());
    }

    /// Undoes every change since the last checkpoint. Recording goes on from the restored state.
    pub fn rollback(&mut self) {
        let Some(log) = self.log.as_mut().map(std::mem::take) else {
            return;
        };
        // In reverse, so a term changed more than once ends on its value at the checkpoint.
        for change in log.into_iter().rev() {
            match change {
                Change::Term(term, Some(coeff)) => {
                    self.terms.insert(term, coeff);
                }
                Change::Term(term, None) => {
                    self.terms.remove(&term);
                }
                Change::Whole(terms) => self.terms = terms,
            }
        }
    }

    /// Stops recording and forgets the changes since the last checkpoint.
    pub fn clear_checkpoint(&mut self) {
        self.log = None;
    }

    /// Records `term`'s current value, before a change, if recording.
    fn note(&mut self, term: &Term) {
        if let Some(log) = &mut self.log {
            log.push(Change::Term(term.clone(), self.terms.get(term).cloned()));
        }
    }

    /// Replaces every term at once (recorded as one change while recording).
    pub fn replace(&mut self, other: Polynomial) {
        let old = std::mem::replace(&mut self.terms, other.terms);
        if let Some(log) = &mut self.log {
            log.push(Change::Whole(old));
        }
    }

    /// Removes the terms that hold `v` and returns them, in term order.
    pub(crate) fn remove_terms_with(&mut self, v: &VarId) -> Vec<(Term, Integer)> {
        let found: Vec<Term> = self
            .terms
            .keys()
            .filter(|t| t.contains(v))
            .cloned()
            .collect();
        found
            .into_iter()
            .map(|term| {
                self.note(&term);
                let coeff = self.terms.remove(&term).expect("a found term is present");
                (term, coeff)
            })
            .collect()
    }

    pub fn from_constant(c: Integer) -> Self {
        let mut terms = BTreeMap::new();
        if !c.is_zero() {
            terms.insert(Term { vars: vec![] }, c);
        }
        Self {
            terms,
            ..Self::default()
        }
    }

    pub fn from_var(v: VarId, c: Integer) -> Self {
        let mut terms = BTreeMap::new();
        if !c.is_zero() {
            terms.insert(Term { vars: vec![v] }, c);
        }
        Self {
            terms,
            ..Self::default()
        }
    }

    pub fn from_vars(vars: Vec<i32>, c: Integer) -> Self {
        let mut terms = BTreeMap::new();
        if !c.is_zero() {
            terms.insert(Term::new(vars), c);
        }
        Self {
            terms,
            ..Self::default()
        }
    }

    pub fn from_term(t: Term, c: Integer) -> Self {
        let mut terms = BTreeMap::new();
        if !c.is_zero() {
            terms.insert(t, c);
        }
        Self {
            terms,
            ..Self::default()
        }
    }

    pub fn size(&self) -> usize {
        self.terms.len()
    }

    pub fn terms(&self) -> &BTreeMap<Term, Integer> {
        &self.terms
    }

    pub fn vars(&self) -> Vec<VarId> {
        self.terms
            .keys()
            .flat_map(|t| t.vars.clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn coeff_of(&self, term: &Term) -> Integer {
        match self.terms.get(term) {
            Some(c) => c.clone(),
            None => Integer::from(0),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn insert(&mut self, term: Term, coeff: Integer) {
        if coeff.is_zero() {
            return;
        }

        self.note(&term);
        match self.terms.entry(term) {
            Entry::Occupied(mut entry) => {
                let c = entry.get_mut();
                *c += coeff;
                if c.is_zero() {
                    entry.remove();
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(coeff);
            }
        }
    }

    pub fn add_assign(&mut self, rhs: Polynomial) {
        for (term, coeff) in rhs.terms {
            self.insert(term, coeff);
        }
    }

    pub fn sub_assign(&mut self, rhs: Polynomial) {
        for (term, coeff) in rhs.terms {
            self.insert(term, -coeff);
        }
    }

    pub fn mul_assign(&mut self, rhs: &Polynomial) {
        if self.is_zero() || rhs.is_zero() {
            self.replace(Polynomial::new());
            return;
        }

        let mut next_map = Polynomial::new();
        for (t1, c1) in self.terms.iter() {
            for (t2, c2) in rhs.terms.iter() {
                let merged_term = t1.mul(t2);
                let prod = Integer::from(c1 * c2);
                next_map.insert(merged_term, prod);
            }
        }
        self.replace(next_map);
    }

    pub fn divide_by_var(&self, v: &VarId) -> Self {
        let t = Term {
            vars: vec![v.clone()],
        };
        self.divide_by_term(&t)
    }

    pub fn divide_by_term(&self, t: &Term) -> Self {
        if t.size() == 0 {
            return self.clone();
        }
        let mut res = Polynomial::new();

        for (m_term, m_coeff) in &self.terms {
            if let Some(new_term) = m_term.div(t) {
                res.terms.insert(new_term, m_coeff.clone());
            }
        }
        res
    }

    pub fn substitute_by_poly(&mut self, v: &VarId, poly: &Polynomial) {
        let mut new_poly = Polynomial::new();
        for (term, coeff) in self.remove_terms_with(v) {
            let new_term = term.remove_var(v).expect("the term holds v");
            new_poly += Polynomial::from_term(new_term, coeff) * poly;
        }
        *self += new_poly;
    }

    pub fn neg_var(&mut self, v: &VarId) {
        let mut extracted_poly = Self::new();
        let found: Vec<Term> = self
            .terms
            .keys()
            .filter(|t| t.contains(v))
            .cloned()
            .collect();
        for term in found {
            self.note(&term);
            let coeff = self.terms.get_mut(&term).expect("a found term is present");
            extracted_poly.insert(term.remove_var(v).expect("the term holds v"), coeff.clone());
            *coeff = -std::mem::take(coeff);
        }
        *self += extracted_poly;
    }

    pub fn neg_coeff(&mut self) {
        if let Some(log) = &mut self.log {
            log.push(Change::Whole(self.terms.clone()));
        }
        for (_, coeff) in self.terms.iter_mut() {
            *coeff = -std::mem::take(coeff);
        }
    }

    pub fn neg_self(&mut self) {
        *self -= Polynomial::from_constant(Integer::from(1));
        self.neg_coeff();
    }

    pub fn mod_by_const(&mut self, n: &Integer) {
        if self.log.is_some() {
            // A truncated remainder changes exactly the coefficients not smaller than n in magnitude.
            let changed: Vec<Term> = self
                .terms
                .iter()
                .filter(|(_, coeff)| coeff.cmp_abs(n) != Ordering::Less)
                .map(|(term, _)| term.clone())
                .collect();
            for term in &changed {
                self.note(term);
            }
        }
        self.terms.retain(|_, coeff| {
            *coeff %= n;
            !coeff.is_zero()
        });
    }

    pub fn remove_mono_by<F>(&mut self, f: F)
    where
        F: Fn(&Term, &Integer) -> bool,
    {
        if self.log.is_none() {
            self.terms.retain(|term, coeff| !f(term, coeff));
            return;
        }
        let removed: Vec<Term> = self
            .terms
            .iter()
            .filter(|(term, coeff)| f(term, coeff))
            .map(|(term, _)| term.clone())
            .collect();
        for term in removed {
            self.note(&term);
            self.terms.remove(&term);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let mut a = Polynomial::new();
        let t1 = Term::new(vec![0]);
        let t2 = Term::new(vec![1, 2]);
        a.insert(t1.clone(), Integer::from(1));
        a.insert(t2.clone(), Integer::from(2));

        let mut b = Polynomial::new();
        b.insert(t1.clone(), Integer::from(-1));
        b.insert(t2.clone(), Integer::from(-3));

        let res = a + b;
        assert_eq!(res.terms.len(), 1);
        assert_eq!(res.coeff_of(&t1), Integer::from(0));
        assert_eq!(format!("{:?}", res), "-1x1*x2");
    }

    #[test]
    fn test_mul() {
        let t1 = Term::new(vec![0]);
        let t2 = Term::new(vec![1]);
        let t3 = Term::new(vec![2]);

        let mut a = Polynomial::new();
        a.insert(t1.clone(), Integer::from(1));
        a.insert(t2.clone(), Integer::from(2));

        let mut b = Polynomial::new();
        b.insert(t1.clone(), Integer::from(2));
        b.insert(t3.clone(), Integer::from(-1));

        let res = a * b;
        assert_eq!(res.terms.len(), 4);
        assert_eq!(format!("{:?}", res), "2x0+4x0*x1-1x0*x2-2x1*x2");
    }

    #[test]
    fn test_neg_var() {
        let a = Polynomial::from_var(0, Integer::from(1));
        let b = Polynomial::from_var(1, Integer::from(1));
        let one = Polynomial::from_constant(Integer::from(1));

        let mut c = (&one - a) * (&one - b);

        c.neg_var(&0);
        c.neg_var(&1);
        assert_eq!(format!("{:?}", c), "1x0*x1");
    }
}
