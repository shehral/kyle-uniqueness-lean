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

Formalization target: Monteiro & Tourky, "The One-Period Kyle Model Has a
Unique Equilibrium" (arXiv:2607.23585v2).

This file is the environment smoke test: it imports the Mathlib modules the
formalization will lean on (Gaussian integrals, Gaussian measures on `ℝ`,
conditional expectation) and proves trivial facts through them, so that
`lake build` failing here means the environment is broken, not the math.

Import notes (mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`, tag
`v4.32.0`): `Mathlib.MeasureTheory.Measure.Gaussian` does NOT exist at this
revision. The Gaussian measure API lives at
`Mathlib.Probability.Distributions.Gaussian.Real` (real line: `gaussianReal`)
and `.Basic` / `.Multivariate` (Banach-space `IsGaussian`, multivariate).
We import `Real` and `Multivariate` — the one-period Kyle model (paper §2,
eqs. (1)–(3)) needs the joint Gaussian structure of the asset value `v` and
noise-trader order flow `u`, and the conditional expectation `E[v ∣ v + u]`.
-/

open MeasureTheory ProbabilityTheory

namespace KyleUniqueness

/-- Smoke test 1: the Gaussian integral `∫ exp (-x²) = √π` is visible.
(Analysis side; used for the pricing-rule regularity arguments, paper §4.) -/
example : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

/-- Smoke test 2: the real Gaussian measure API is visible. `gaussianReal m v`
is the Gaussian law on `ℝ` with mean `m` and variance `v ≥ 0`; the
noise-trader order flow `u ~ N(0, σᵤ²)` of the Kyle model (paper §2) will be
modeled with it. -/
example : gaussianReal 0 1 Set.univ = 1 := by
  simp

/-- Smoke test 3: `gaussianReal` is a probability measure for any
mean/variance. -/
example (m : ℝ) (v : NNReal) : IsProbabilityMeasure (gaussianReal m v) :=
  inferInstance

end KyleUniqueness
