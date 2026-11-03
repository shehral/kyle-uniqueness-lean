/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# KyleUniqueness — environment smoke test

Formalization target: Monteiro & Tourky, *The one-period Kyle model has one
equilibrium* (arXiv:2607.23585, **v4** of 2026-08-20).

**Version note.** This file was written in the v2 session and its comments
were keyed to the v2 title ("The One-Period Kyle Model Has a Unique
Equilibrium") and to v2's flat equation numbering; it is re-keyed to v4 here.
Earlier sessions of this development were keyed to v3; the full v3 → v4
crosswalk is `STATEMENT_NOTES.md` §1, and the repo-wide policy is
`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision D1.

This file is the environment smoke test: it imports the Mathlib modules the
formalization will lean on (Gaussian integrals, Gaussian measures on `ℝ`,
conditional expectation) and proves trivial facts through them, so that
`lake build` failing here means the environment is broken, not the math.

Import notes (mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`, tag
`v4.32.0`): `Mathlib.MeasureTheory.Measure.Gaussian` does NOT exist at this
revision. The Gaussian measure API lives at
`Mathlib.Probability.Distributions.Gaussian.Real` (real line: `gaussianReal`)
and `.Basic` / `.Multivariate` (Banach-space `IsGaussian`, multivariate).
We import `Real` and `Multivariate` — the one-period Kyle model (v4 §1; the
v2 numbering "eqs. (1)–(3)" used here originally has no v4 counterpart, since
v4 states the primitives in prose and numbers only the equilibrium pair
(1.1)/(1.2)) needs the joint Gaussian structure of the asset value `v` and
noise-trader order flow `u`, and the conditional expectation `E[v ∣ v + u]`.
-/

open MeasureTheory ProbabilityTheory

namespace KyleUniqueness

/-- Smoke test 1: the Gaussian integral `∫ exp (-x²) = √π` is visible.
(Analysis side; used for the pricing-rule regularity arguments, v4 §2.3 and
Appendix A — the "paper §4" of the original v2 comment is *not* v4 §4, which
is the sharp-bounds section.) -/
example : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

/-- Smoke test 2: the real Gaussian measure API is visible. `gaussianReal m v`
is the Gaussian law on `ℝ` with mean `m` and variance `v ≥ 0`; the
noise-trader order flow `u ~ N(0, σ²)` of the Kyle model (v4 §1) will be
modeled with it. -/
example : gaussianReal 0 1 Set.univ = 1 := by
  simp

/-- Smoke test 3: `gaussianReal` is a probability measure for any
mean/variance. -/
example (m : ℝ) (v : NNReal) : IsProbabilityMeasure (gaussianReal m v) :=
  inferInstance

end KyleUniqueness
