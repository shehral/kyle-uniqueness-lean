/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Regularity

/-!
# Posterior differentiation, `C¹` legs (blueprint node D1, part; v3 Lemma 4.1)

The differentiation-under-the-integral legs of v3 Lemma 4.1: the flow
density `p(y) = E[ϱ(y − φ(V))]` and the numerator
`n(y) = E[V·ϱ(y − φ(V))]` are differentiable in `y` with the expected
kernel derivatives, and hence the inverse regression `P = n/p` is
differentiable with the quotient formula. Dominants are trivial against
the Gaussian prior: `|t|ϱ(t) ≤ 2e^{1/2}(√(2π))⁻¹` uniformly
(`abs_mul_gaussianPDFReal_std_le` + `gaussianPDFReal_le`), so the constant
resp. `|v|`-linear majorants integrate against `N(0,1)`.

**Not yet here** (the rest of D1 and D2, gated on B2's strict
monotonicity): the covariance representation `P′(y) = Cov_{π_y}(id, φ)`,
its strict positivity, and `F′ > 0`.
-/

open MeasureTheory ProbabilityTheory Real Filter Set

open scoped ENNReal NNReal Topology

namespace KyleUniqueness

/-- Uniform bound for the first-moment kernel:
`|t|·ϱ(t) ≤ 2e^{1/2}·(√(2π))⁻¹`. -/
lemma abs_mul_gaussianPDFReal_std_le_const (t : ℝ) :
    |t| * gaussianPDFReal 0 1 t ≤ 2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹ := by
  refine le_trans (abs_mul_gaussianPDFReal_std_le t) ?_
  have h1 : gaussianPDFReal 0 1 (t - 1) ≤ (√(2 * π))⁻¹ := by
    have h := gaussianPDFReal_le 0 1 (t - 1)
    simpa using h
  have h2 : gaussianPDFReal 0 1 (t + 1) ≤ (√(2 * π))⁻¹ := by
    have h := gaussianPDFReal_le 0 1 (t + 1)
    simpa using h
  have h3 := add_le_add h1 h2
  calc Real.exp (1/2 : ℝ)
      * (gaussianPDFReal 0 1 (t - 1) + gaussianPDFReal 0 1 (t + 1))
      ≤ Real.exp (1/2 : ℝ) * ((√(2 * π))⁻¹ + (√(2 * π))⁻¹) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹ := by ring

/-- Node D1, `p`-leg: the flow density is differentiable with
`p′(y) = −E[(y − φ(V))·ϱ(y − φ(V))]`. -/
theorem hasDerivAt_flowDensity {φ : ℝ → ℝ} (hφ : Measurable φ) (y₀ : ℝ) :
    HasDerivAt (flowDensity φ)
      (∫ v, -((y₀ - φ v) * stdNormalPDF (y₀ - φ v)) ∂gaussianReal 0 1)
      y₀ := by
  have hker : ∀ y : ℝ, Measurable fun v => stdNormalPDF (y - φ v) := fun y =>
    (continuous_gaussianPDFReal 0 1).measurable.comp (measurable_const.sub hφ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1)
    (F := fun y v => stdNormalPDF (y - φ v))
    (F' := fun y v => -((y - φ v) * stdNormalPDF (y - φ v)))
    (bound := fun _ => 2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹)
    (Metric.ball_mem_nhds y₀ one_pos)
    (Eventually.of_forall fun y => (hker y).aestronglyMeasurable)
    ?_ ?_ ?_ (integrable_const _) ?_
  · exact key.2
  · -- integrability of the `p`-integrand at `y₀`
    refine Integrable.mono' (integrable_const ((√(2 * π))⁻¹))
      (hker y₀).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, stdNormalPDF,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)]
    simpa using gaussianPDFReal_le 0 1 (y₀ - φ v)
  · -- measurability of the derivative kernel at `y₀`
    exact (((measurable_const.sub hφ).mul (hker y₀)).neg).aestronglyMeasurable
  · -- the uniform bound
    refine ae_of_all _ fun v y _ => ?_
    rw [Real.norm_eq_abs, abs_neg, abs_mul, stdNormalPDF,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)]
    exact abs_mul_gaussianPDFReal_std_le_const (y - φ v)
  · -- pointwise differentiability in `y`
    refine ae_of_all _ fun v y _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => y - φ v) 1 y :=
      (hasDerivAt_id y).sub_const (φ v)
    have h2 := (hasDerivAt_gaussianPDFReal_std (y - φ v)).comp y h1
    have heq : -(y - φ v) * gaussianPDFReal 0 1 (y - φ v) * 1
        = -((y - φ v) * stdNormalPDF (y - φ v)) := by
      rw [stdNormalPDF]; ring
    rw [← heq]
    exact h2

/-- Node D1, `n`-leg: the posterior-mean numerator
`n(y) = E[V·ϱ(y − φ(V))]` is differentiable with
`n′(y) = −E[V·(y − φ(V))·ϱ(y − φ(V))]`. -/
theorem hasDerivAt_flowNumerator {φ : ℝ → ℝ} (hφ : Measurable φ) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1)
      (∫ v, -(v * ((y₀ - φ v) * stdNormalPDF (y₀ - φ v))) ∂gaussianReal 0 1)
      y₀ := by
  have hker : ∀ y : ℝ, Measurable fun v => v * stdNormalPDF (y - φ v) :=
    fun y => measurable_id.mul
      ((continuous_gaussianPDFReal 0 1).measurable.comp
        (measurable_const.sub hφ))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1)
    (F := fun y v => v * stdNormalPDF (y - φ v))
    (F' := fun y v => -(v * ((y - φ v) * stdNormalPDF (y - φ v))))
    (bound := fun v => |v| * (2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹))
    (Metric.ball_mem_nhds y₀ one_pos)
    (Eventually.of_forall fun y => (hker y).aestronglyMeasurable)
    ?_ ?_ ?_
    (((integrable_id_gaussianReal 0 1).abs).mul_const
      (2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹)) ?_
  · exact key.2
  · refine Integrable.mono'
      ((integrable_id_gaussianReal 0 1).abs.const_mul ((√(2 * π))⁻¹))
      (hker y₀).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_mul, stdNormalPDF,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)]
    calc |v| * gaussianPDFReal 0 1 (y₀ - φ v)
        ≤ |v| * (√(2 * π))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg v)
          simpa using gaussianPDFReal_le 0 1 (y₀ - φ v)
      _ = (√(2 * π))⁻¹ * |id v| := by rw [mul_comm]; rfl
  · exact ((measurable_id.mul ((measurable_const.sub hφ).mul
      ((continuous_gaussianPDFReal 0 1).measurable.comp
        (measurable_const.sub hφ)))).neg).aestronglyMeasurable
  · refine ae_of_all _ fun v y _ => ?_
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg v)
    rw [abs_mul, stdNormalPDF,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)]
    exact abs_mul_gaussianPDFReal_std_le_const (y - φ v)
  · refine ae_of_all _ fun v y _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => y - φ v) 1 y :=
      (hasDerivAt_id y).sub_const (φ v)
    have h2 := ((hasDerivAt_gaussianPDFReal_std (y - φ v)).comp y h1).const_mul v
    have heq : v * (-(y - φ v) * gaussianPDFReal 0 1 (y - φ v) * 1)
        = -(v * ((y - φ v) * stdNormalPDF (y - φ v))) := by
      rw [stdNormalPDF]; ring
    rw [← heq]
    exact h2

/-- Node D1, quotient leg: the inverse regression `P = n/p` is
differentiable, with the quotient-rule formula in terms of the two kernel
derivatives. (The covariance form `P′(y) = Cov_{π_y}(id, φ)` and its
positivity are the remaining D1 obligations, gated on B2.) -/
theorem hasDerivAt_inverseRegression {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y₀ : ℝ) :
    HasDerivAt (inverseRegression φ)
      (((∫ v, -(v * ((y₀ - φ v) * stdNormalPDF (y₀ - φ v))) ∂gaussianReal 0 1)
          * flowDensity φ y₀
        - (∫ v, v * stdNormalPDF (y₀ - φ v) ∂gaussianReal 0 1)
          * ∫ v, -((y₀ - φ v) * stdNormalPDF (y₀ - φ v)) ∂gaussianReal 0 1)
        / (flowDensity φ y₀) ^ 2) y₀ := by
  have hn := hasDerivAt_flowNumerator hφ y₀
  have hp := hasDerivAt_flowDensity hφ y₀
  have hp0 : flowDensity φ y₀ ≠ 0 := (lemma21_flowDensity_pos hφ y₀).ne'
  have h := hn.div hp hp0
  have heq : inverseRegression φ = fun y =>
      (∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1)
        / flowDensity φ y := by
    funext y
    rw [inverseRegression]
  rw [heq]
  exact h

end KyleUniqueness
