use super::{ReductionEngine, SizeGuard, Substitution, VarDomain};
use crate::{
    Result,
    bipoly::{Polynomial, VarId},
};

use rand::{seq::SliceRandom, thread_rng};
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

const PROBE_ABORT_RATIO: usize = 5;

pub enum ReductionAction {
    Reduce(VarId),
    Skip,
    Stop,
}

pub trait ReductionPolicy {
    fn next_action(&mut self, _engine: &mut ReductionEngine) -> Result<ReductionAction>;
}

pub struct DefaultPolicy;
impl ReductionPolicy for DefaultPolicy {
    fn next_action(&mut self, engine: &mut ReductionEngine) -> Result<ReductionAction> {
        if let Some(var) = engine.state.var_domain.candidates().last() {
            Ok(ReductionAction::Reduce(*var))
        } else {
            Ok(ReductionAction::Stop)
        }
    }
}

pub struct RandomPolicy;
impl ReductionPolicy for RandomPolicy {
    fn next_action(&mut self, engine: &mut ReductionEngine) -> Result<ReductionAction> {
        if let Some(v) = engine
            .state
            .var_domain
            .candidates()
            .choose(&mut thread_rng())
        {
            Ok(ReductionAction::Reduce(*v))
        } else {
            Ok(ReductionAction::Stop)
        }
    }
}

pub struct LazyGreedyPolicy {
    max_ratio: f64,
    penalty: HashMap<VarId, u32>,
}

impl ReductionPolicy for LazyGreedyPolicy {
    fn next_action(&mut self, engine: &mut ReductionEngine) -> Result<ReductionAction> {
        let candidates = engine.state.var_domain.candidates();
        if candidates.len() == 0 {
            return Ok(ReductionAction::Stop);
        } else if candidates.len() == 1 {
            return Ok(ReductionAction::Reduce(candidates[0]));
        }

        // The candidates in (key, variable) order, taken one at a time: most decisions accept
        // one of the first, so they are not all sorted.
        let mut candidates = self.sort_queue_by_occ_penalty(
            &candidates,
            &engine.state.poly,
            &engine.ctx.substitutions,
        );
        let Some(&Reverse((_, first_candidate))) = candidates.peek() else {
            return Ok(ReductionAction::Stop);
        };
        let current_size = engine.state.poly.size();
        let mut best_candidate: Option<(f64, VarId)> = None;

        let guard = SizeGuard::new(current_size.saturating_mul(PROBE_ABORT_RATIO));
        let checkpoint = engine.checkpoint();
        while let Some(Reverse((_, var))) = candidates.pop() {
            if let Err(err) = engine.reduce_var(var, Some(&guard)) {
                debug_step!(engine.name; fallback; "Probing failed", var; "Error: {:?}", err);
                engine.restore(&checkpoint);
                continue;
            }
            let ratio =
                (engine.state.poly.size() as f64 - current_size as f64) / current_size as f64;
            debug_step!(
                engine.name; probe; "Probing size", engine.state.poly.size();
                "Ratio: {:.3}", ratio
            );
            if ratio < self.max_ratio {
                engine.release_checkpoint();
                debug_step!(engine.name; progress; "Chosen var", var; "Action: Skip");
                return Ok(ReductionAction::Skip);
            } else {
                let value = self.penalty.entry(var).or_insert(1);
                *value = value.saturating_mul(2);
                if best_candidate.is_none_or(|(best_ratio, _)| ratio < best_ratio) {
                    best_candidate = Some((ratio, var));
                }
                engine.restore(&checkpoint);
            }
        }
        engine.release_checkpoint();
        if let Some((_, var)) = best_candidate {
            debug_step!(engine.name; progress; "Chosen var", var; "Action: Replace");
            // Every probe was undone: replay the best one, under the guard its probe passed,
            // instead of keeping a copy of its state.
            engine.reduce_var(var, Some(&guard))?;
            return Ok(ReductionAction::Skip);
        } else {
            return Ok(ReductionAction::Reduce(first_candidate));
        }
    }
}

impl LazyGreedyPolicy {
    pub fn new(max_ratio: f64) -> Self {
        LazyGreedyPolicy {
            max_ratio,
            penalty: HashMap::new(),
        }
    }

    fn sort_queue_by_occ_penalty(
        &mut self,
        candidates: &[VarId],
        poly: &Polynomial,
        substitutions: &HashMap<VarId, Substitution>,
    ) -> BinaryHeap<Reverse<(u32, VarId)>> {
        let mut stats: Vec<(_, u32)> = candidates.iter().map(|&v| (v, 0)).collect();

        if let Some(counts) = stats
            .iter()
            .map(|&(v, _)| poly.occurrences(v))
            .collect::<Option<Vec<u32>>>()
        {
            for (stat, count) in stats.iter_mut().zip(counts) {
                stat.1 = count;
            }
        } else {
            stats.sort_by_key(|(v, _)| *v);
            Self::count_occurrences(&mut stats, poly);
        }

        // Each key once (a comparison sort would evaluate it, with its two map look-ups, at every
        // comparison). Ordering by (key, variable) is the stable order by key of the candidates
        // sorted by variable; a heap is built in linear time and yields that order.
        stats
            .into_iter()
            .map(|(v, count)| {
                let sub_size = substitutions.get(&v).map(|s| s.size()).unwrap_or(0) as u32;
                let penalty = *self.penalty.entry(v).or_insert(1);
                Reverse((count.saturating_mul(sub_size).saturating_mul(penalty), v))
            })
            .collect()
    }

    /// Counts, for each candidate of `stats` (sorted by variable), the terms of `poly` holding it.
    fn count_occurrences(stats: &mut [(VarId, u32)], poly: &Polynomial) {
        let min_q = stats.first().unwrap().0;
        let max_q = stats.last().unwrap().0;

        for term in poly.terms.keys() {
            let vars = term.vars();
            if vars.is_empty() || *vars.last().unwrap() < min_q {
                continue;
            }
            if vars[0] > max_q {
                break;
            }

            let (mut i, mut j) = (0, 0);
            while i < stats.len() && j < vars.len() {
                let target = stats[i].0;
                let current = vars[j];

                if target == current {
                    stats[i].1 += 1;
                    i += 1;
                    j += 1;
                } else if current < target {
                    j += 1;
                } else {
                    i += 1;
                }
            }
        }
    }
}
