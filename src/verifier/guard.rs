use crate::bipoly::{Polynomial, Term, VarId};

use rug::Integer;
use std::fmt::{Debug, Display, Formatter};

pub struct SizeGuard {
    max_terms: usize,
}

pub struct SizeLimitExceeded {
    pub size: usize,
    pub limit: usize,
}

impl SizeGuard {
    pub fn new(max_terms: usize) -> Self {
        Self { max_terms }
    }

    pub fn check(&self, size: usize) -> Result<(), SizeLimitExceeded> {
        if size > self.max_terms {
            Err(SizeLimitExceeded {
                size,
                limit: self.max_terms,
            })
        } else {
            Ok(())
        }
    }
}

impl Debug for SizeLimitExceeded {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self)
    }
}
impl Display for SizeLimitExceeded {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "Size limit {} exceeded.", self.limit)
    }
}

impl std::error::Error for SizeLimitExceeded {}

impl Polynomial {
    pub fn insert_checked(
        &mut self,
        term: Term,
        coeff: Integer,
        guard: &SizeGuard,
    ) -> Result<(), SizeLimitExceeded> {
        self.insert(term, coeff);
        guard.check(self.size())?;
        Ok(())
    }
    pub fn add_assign_checked(
        &mut self,
        rhs: Polynomial,
        guard: &SizeGuard,
    ) -> Result<(), SizeLimitExceeded> {
        for (term, coeff) in rhs.terms {
            self.insert_checked(term, coeff, guard)?
        }
        Ok(())
    }

    pub fn sub_assign_checked(
        &mut self,
        rhs: Polynomial,
        guard: &SizeGuard,
    ) -> Result<(), SizeLimitExceeded> {
        for (term, coeff) in rhs.terms {
            self.insert_checked(term, -coeff, guard)?;
        }
        Ok(())
    }

    pub fn mul_assign_checked(
        &mut self,
        rhs: &Polynomial,
        guard: &SizeGuard,
    ) -> Result<(), SizeLimitExceeded> {
        if self.is_zero() || rhs.is_zero() {
            self.replace(Polynomial::new());
            return Ok(());
        }

        let mut next_map = Polynomial::new();
        for (t1, c1) in self.terms.iter() {
            for (t2, c2) in rhs.terms.iter() {
                let merged_term = t1.mul(t2);
                let prod = Integer::from(c1 * c2);
                next_map.insert_checked(merged_term, prod, guard)?
            }
        }
        self.replace(next_map);
        Ok(())
    }

    /// [`substitute_by_poly`](Polynomial::substitute_by_poly) under `guard`.
    pub fn substitute_by_poly_checked(
        &mut self,
        v: &VarId,
        poly: &Polynomial,
        guard: &SizeGuard,
    ) -> Result<Vec<Term>, SizeLimitExceeded> {
        let mut new_poly = Polynomial::new();
        for (term, coeff) in self.remove_terms_with(v) {
            let new_term = term.remove_var(v).expect("the term holds v");
            new_poly += Polynomial::from_term(new_term, coeff) * poly;
        }
        let touched = new_poly.terms.keys().cloned().collect();
        self.add_assign_checked(new_poly, guard)?;
        Ok(touched)
    }
}
