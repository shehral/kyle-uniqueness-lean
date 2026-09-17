/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Identity-theorem spike (blueprint Tier 0.4, de-risking hard block 5)

The rigidity endgame of the paper as it stood in **v2** (v2 Theorem 3.1 —
a v2-only number with no v3 or v4 counterpart; blueprint node L2) needs:
a real-analytic `G : ℝ → ℝ` whose zero set carries positive mass under an
atomless law must vanish identically. This file proves exactly that chain
against the pin, verifying that the only API uncertainty flagged in
`blueprint/attack_order.md` (the `AccPt → ∃ᶠ` glue) is a one-lemma
rewrite:

* `accPt_iff_frequently_nhdsNE` (Topology/ClusterPt.lean) converts an
  accumulation point of the zero set into the `∃ᶠ z in 𝓝[≠] x₀, G z = 0`
  hypothesis of the identity theorem;
* `exists_accPt_of_nullSingletonClass` (already at the pin — discovered
  during the `GaussianHelpers` audit) produces the accumulation point from
  positive measure, replacing the "positive measure ⇒ infinite ⇒
  Bolzano–Weierstrass" route the blueprint had budgeted;
* `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`
  (Analysis/Analytic/IsolatedZeros.lean) is the identity theorem itself.

Consequence for the campaign: hard block 5's L2 node loses its API risk
entirely; what remains there is the `F/x` ODE patch and the pushforward
atomlessness, both routine.

**Version note (v3 recorded 2026-08-12; re-checked against v4
2026-09-16).** arXiv:2607.23585**v3** REMOVED the complex-analytic rigidity
endgame from the paper ("The proof is probabilistic and convex-analytic and
uses no complex analysis"), and **v4** (2026-08-20) did not bring it back —
v4 additionally deleted v3's Appendix B scope lemma and v3 eqs. (30)–(32)
outright. So this spike's consumer (blueprint node L2 / v2 Theorem 3.1) no
longer exists in the v3 or the v4 proof plan.

The file is retained as proved, Mathlib-only infrastructure (potential
upstream material); it is **NOT part of the claim surface of v3 or v4**.
Crosswalk: `V4_DELTA_REPORT_2026-09-16.md` §1; policy:
`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision D1.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace KyleUniqueness

/-- Identity theorem, accumulation-point form: a real-analytic function on
`ℝ` whose zero set has an accumulation point vanishes identically.
(The `AccPt → ∃ᶠ` glue is `accPt_iff_frequently_nhdsNE`.) -/
theorem analyticOnNhd_eq_zero_of_accPt {G : ℝ → ℝ}
    (hG : AnalyticOnNhd ℝ G Set.univ) {x₀ : ℝ}
    (hacc : AccPt x₀ (𝓟 {x | G x = 0})) : ∀ x, G x = 0 := by
  have hfreq : ∃ᶠ z in 𝓝[≠] x₀, G z = 0 :=
    accPt_iff_frequently_nhdsNE.mp hacc
  have h := hG.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ x₀) hfreq
  exact fun x => h (Set.mem_univ x)

/-- The L2 endgame chain: a real-analytic function on `ℝ` whose zero set
has positive measure under an atomless measure vanishes identically.
(In node L2 the measure is the law of `φ(V)`, atomless because `φ` is
strictly monotone and the Gaussian law of `V` is atomless.) -/
theorem analyticOnNhd_eq_zero_of_measure_ne_zero {G : ℝ → ℝ}
    (hG : AnalyticOnNhd ℝ G Set.univ) {μ : Measure ℝ} [NullSingletonClass μ]
    (hμ : μ {x | G x = 0} ≠ 0) : ∀ x, G x = 0 := by
  obtain ⟨x₀, hacc⟩ := exists_accPt_of_nullSingletonClass
    (E := {x | G x = 0}) (pos_iff_ne_zero.mpr hμ)
  exact analyticOnNhd_eq_zero_of_accPt hG hacc

end KyleUniqueness
