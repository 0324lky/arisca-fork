use super::topo::DomainCheckpoint;
use super::{
    FlipManager, ReductionAction, ReductionContext, ReductionMeta, ReductionPolicy, ReductionState,
    SizeGuard, Substitution, VarDomain, process_cone,
};
use crate::Result;
use crate::bipoly::{Polynomial, Term, VarId};
use crate::json::ToJson;


pub struct ReductionEngine<'a> {
    pub name: String,
    pub ctx: &'a ReductionContext<'a>,
    pub state: ReductionState,
    pub size_limit: Option<usize>,
    /// Every term was normalized by the last normalization (it was a full one, or only touched
    /// terms changed since one): a later normalization may then check the touched terms only.
    normalized: bool,
}

/// The vanishing-monomial rule: a term holding two consecutive negative variables is zero.
fn vanishes(term: &Term) -> bool {
    for pair in term.vars().windows(2) {
        let (var_i, var_j) = (pair[0], pair[1]);
        if var_j >= 0 {
            return false;
        } else if (var_j - var_i) == 1 {
            return true;
        }
    }
    false
}

/// The engine at a point it can return to (see [`ReductionEngine::checkpoint`]).
pub struct Checkpoint {
    var_domain: DomainCheckpoint,
    flip_manager: Option<FlipManager>,
    seq_len: usize,
    sizes_len: usize,
    normalized: bool,
}

impl<'a> ReductionEngine<'a> {
    /// Marks the current state for [`restore`](Self::restore): the polynomial and the candidate
    /// domain record their changes from here on (a probe touches few of their entries), the
    /// small fields are copied.
    pub fn checkpoint(&mut self) -> Checkpoint {
        self.state.poly.checkpoint();
        Checkpoint {
            var_domain: self.state.var_domain.checkpoint(),
            flip_manager: self.state.flip_manager.clone(),
            seq_len: self.state.global_seq.len(),
            sizes_len: self.state.poly_sizes.len(),
            normalized: self.normalized,
        }
    }

    /// Returns to the state at `checkpoint`; the polynomial goes on recording from there.
    pub fn restore(&mut self, checkpoint: &Checkpoint) {
        self.state.poly.rollback();
        self.state.var_domain.restore(&checkpoint.var_domain);
        self.state.flip_manager = checkpoint.flip_manager.clone();
        self.state.global_seq.truncate(checkpoint.seq_len);
        self.state.poly_sizes.truncate(checkpoint.sizes_len);
        self.normalized = checkpoint.normalized;
    }

    /// Keeps the current state and stops recording.
    pub fn release_checkpoint(&mut self) {
        self.state.poly.clear_checkpoint();
        self.state.var_domain.clear_checkpoint();
    }

    pub fn new(
        name: impl Into<String>,
        ctx: &'a ReductionContext,
        state: ReductionState,
        size_limit: Option<usize>,
    ) -> Self {
        Self {
            name: name.into(),
            ctx,
            state,
            size_limit,
            normalized: false,
        }
    }

    /// Reduces every coefficient modulo the output range and drops vanishing monomials. After a
    /// full pass only the terms a substitution touched can need either, so with occurrence
    /// counts (the main polynomial) and a small update only those are checked.
    fn normalize(&mut self, touched: &[Term]) {
        let poly = &mut self.state.poly;
        if self.normalized
            && poly.tracks_occurrences()
            && self.state.flip_manager.is_none()
            && touched.len() * 8 <= poly.size()
        {
            poly.normalize_terms(touched, self.ctx.modulus, vanishes);
            return;
        }
        if let Some(modulus) = self.ctx.modulus {
            poly.mod_by_const(modulus);
        }
        poly.remove_mono_by(|term, _| vanishes(term));
        self.normalized = true;
    }

    fn write_partial_meta(&self) -> Result<()> {
        if self.name != "MAIN" {
            return Ok(());
        }
        if let Some(out_path) = &self.ctx.cfg.meta_file {
            ReductionMeta::new(self.ctx.vars, &self.state.global_seq, &self.state.poly_sizes)
                .write_json(out_path)?;
        }
        Ok(())
    }

    fn apply_reduction(
        &mut self,
        var: VarId,
        gate_poly: Polynomial,
        guard: Option<&SizeGuard>,
    ) -> Result<()> {
        debug_step!(self.name; step; "Reducing var", var; "Poly size: {}", gate_poly.size());
        let new_vars = gate_poly.vars();
        let gate_poly = if let Some(fm) = &self.state.flip_manager {
            fm.normalize(&var, &new_vars, &gate_poly)
        } else {
            gate_poly
        };

        let touched = if let Some(guard) = guard {
            self.state
                .poly
                .substitute_by_poly_checked(&var, &gate_poly, guard)?
        } else {
            self.state.poly.substitute_by_poly(&var, &gate_poly)
        };

        self.normalize(&touched);

        if let Some(fm) = &mut self.state.flip_manager {
            fm.greedy_flip(&mut self.state.poly, &new_vars);
        }
        Ok(())
    }

    fn resolve_substitution(
        &mut self,
        var: VarId,
        guard: Option<&SizeGuard>,
    ) -> Result<Option<Polynomial>> {
        match self.ctx.substitutions.get(&var) {
            Some(Substitution::Poly(p)) => Ok(Some(p.clone())),
            Some(Substitution::Cone(cone, is_conv, base_poly)) => {
                self.apply_reduction(var, base_poly.clone(), guard)?;
                let (new_poly, cone_seq, poly_sizes) = process_cone(
                    cone,
                    self.state.poly.clone(),
                    *is_conv,
                    self.ctx,
                    self.size_limit,
                    self.state.flip_manager.as_mut(),
                )?;
                self.state.poly.replace(new_poly);
                self.normalized = false;
                self.state.global_seq.extend(cone_seq);
                self.state.poly_sizes.extend(poly_sizes);
                Ok(None)
            }
            None => Ok(None),
        }
    }

    pub fn reduce_var(&mut self, var: VarId, guard: Option<&SizeGuard>) -> Result<()> {
        self.state.var_domain.update(var);

        self.state.global_seq.push(var);

        if let Some(gate_poly) = self.resolve_substitution(var, guard)? {
            self.apply_reduction(var, gate_poly, guard)?;
        };

        self.state.poly_sizes.push(self.state.poly.size());

        Ok(())
    }

    pub fn run(mut self, policy: &mut dyn ReductionPolicy) -> Result<ReductionState> {
        let mut curr = 0;
        debug_step!(self.name; event; "Starting engine execution...");
        loop {
            self.ctx.check_cancelled()?;
            match policy.next_action(&mut self)? {
                ReductionAction::Stop => {
                    debug_step!(self.name; event; "Engine execution stopped.");
                    break;
                }
                ReductionAction::Reduce(var) => {
                    if let Err(err) = self.reduce_var(var, None) {
                        self.write_partial_meta()?;
                        return Err(err);
                    }
                }
                ReductionAction::Skip => {}
            }

            curr += 1;
            debug_step!(
                self.name; progress; "Progress", format!("{}/{}", curr, self.state.var_domain.len());
                "Current size: {}", self.state.poly.size()
            );

            if let Some(size_limit) = self.size_limit {
                if self.state.poly.size() > size_limit {
                    self.write_partial_meta()?;
                    return Err(format!("Size limit exceeded: {:?}", self.state.poly.size()).into());
                }
            }
        }
        Ok(self.state)
    }
}
