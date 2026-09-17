/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Statement

/-!
# Regularity of the Gaussian smoothing `F` (blueprint node R2; v4 Lemma 2.3)

Keyed to Monteiro & Tourky, *The one-period Kyle model has one equilibrium*
(arXiv:2607.23585, **v4** of 2026-08-20). This module was written in the v3
session; its numbering is re-keyed to v4 here (crosswalk:
`V4_DELTA_REPORT_2026-09-16.md` §1; policy:
`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision D1). Lemma 2.3 keeps its
number from v3, but v3's eq. (4) is v4's **(2.2)** and v3's eq. (5) is v4's
**(2.3)** — and v4 tags only the FIRST line of that split display, so the
`u`-integral form below carries no v4 equation number of its own.

v4 Lemma 2.3's regularity clause: `F(x) = E[P(x + U)]` is continuously
differentiable with

`F′(x) = ∫ P(y)·(y − x)·ϱ(y − x) dy = ∫ u·P(x + u)·ϱ(u) du`   (eq. (2.3))

for every Borel strategy `φ` — no moment hypotheses (node R1 =
`lemma23_integrable`, proved, supplies all integrability). The route is the
ℝ-only differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le` at `𝕜 = ℝ`) with the
exp-shift majorant

`|y − x|·ϱ(y − x) ≤ 2e^{5/2}·(ϱ(y − x₀ − 2) + ϱ(y − x₀ + 2))`  (`|x − x₀| ≤ 1`)

built from the algebraic shift identity `e^{ct}ϱ(t) = e^{c²/2}ϱ(t − c)` —
no complex analysis anywhere (v2's hard block 1 stays dead).

Main statements:
* `gaussianSmoothing_eq_convolution` — eq. (2.2),
  `F(x) = ∫ P(y)ϱ(y − x) dy`;
* `hasDerivAt_gaussianSmoothing` + `integrable_gaussianSmoothing_deriv_kernel`
  — differentiability with the eq.-(2.3) kernel;
* `deriv_gaussianSmoothing_eq_prob` — the probabilistic form of eq. (2.3);
* `continuous_gaussianSmoothing_deriv` (+ `deriv_gaussianSmoothing`,
  `continuous_deriv_gaussianSmoothing`) — `F ∈ C¹`.

Lemma 2.3's remaining bookkeeping clause (`F(φ(V)) = E[E[V∣Y]∣V]` a.s.) is
E2's input and is deferred to the resampling file with the rest of the
condExp plumbing.

**Scope caveat against v4.** v4's Lemma 2.3 is strictly STRONGER than v3's:
besides the `C¹` regularity and the two integral formulas proved here, it
asserts finiteness of the expectation in (2.1) and absolute convergence of
the integrals in (2.2)/(2.3). Those extra conclusions are supplied elsewhere
in the tree — `lemma23_integrable` (`Statement.lean`),
`integrable_gaussianSmoothing_deriv_kernel` below,
`KyleModel.integrable_Q_comp_add` (`CondExpBridge.lean`) and
`integrable_inverseRegression_const_add` — so this module alone discharges a
proper SUBSET of v4 Lemma 2.3.
-/

open MeasureTheory ProbabilityTheory Real Filter Set

open scoped ENNReal NNReal Topology

namespace KyleUniqueness

/-! ## The exp-shift majorant -/

/-- Shift identity for the standard normal density:
`e^{ct}·ϱ(t) = e^{c²/2}·ϱ(t − c)`. -/
lemma exp_mul_gaussianPDFReal_std (c t : ℝ) :
    Real.exp (c * t) * gaussianPDFReal 0 1 t
      = Real.exp (c ^ 2 / 2) * gaussianPDFReal 0 1 (t - c) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_left_comm, mul_left_comm (Real.exp (c ^ 2 / 2)), ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- First-moment majorant:
`|t|·ϱ(t) ≤ e^{1/2}·(ϱ(t − 1) + ϱ(t + 1))`. -/
lemma abs_mul_gaussianPDFReal_std_le (t : ℝ) :
    |t| * gaussianPDFReal 0 1 t
      ≤ Real.exp (1/2 : ℝ)
        * (gaussianPDFReal 0 1 (t - 1) + gaussianPDFReal 0 1 (t + 1)) := by
  have h0 : (0:ℝ) ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
  have h1 : |t| ≤ Real.exp t + Real.exp (-t) := by
    rcases le_total 0 t with ht | ht
    · calc |t| = t := abs_of_nonneg ht
        _ ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
        _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
    · calc |t| = -t := abs_of_nonpos ht
        _ ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
        _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le
  have e1 : Real.exp t * gaussianPDFReal 0 1 t
      = Real.exp (1/2 : ℝ) * gaussianPDFReal 0 1 (t - 1) := by
    have h := exp_mul_gaussianPDFReal_std 1 t
    norm_num at h
    exact h
  have e2 : Real.exp (-t) * gaussianPDFReal 0 1 t
      = Real.exp (1/2 : ℝ) * gaussianPDFReal 0 1 (t + 1) := by
    have h := exp_mul_gaussianPDFReal_std (-1) t
    norm_num [sub_neg_eq_add] at h
    exact h
  calc |t| * gaussianPDFReal 0 1 t
      ≤ (Real.exp t + Real.exp (-t)) * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = Real.exp t * gaussianPDFReal 0 1 t
        + Real.exp (-t) * gaussianPDFReal 0 1 t := add_mul _ _ _
    _ = Real.exp (1/2 : ℝ) * gaussianPDFReal 0 1 (t - 1)
        + Real.exp (1/2 : ℝ) * gaussianPDFReal 0 1 (t + 1) := by rw [e1, e2]
    _ = Real.exp (1/2 : ℝ)
        * (gaussianPDFReal 0 1 (t - 1) + gaussianPDFReal 0 1 (t + 1)) :=
        (mul_add _ _ _).symm

/-- Shift absorption: for `|s| ≤ 2`,
`ϱ(t − s) ≤ e²·(ϱ(t − 2) + ϱ(t + 2))`. -/
lemma gaussianPDFReal_std_shift_le {s : ℝ} (hs : |s| ≤ 2) (t : ℝ) :
    gaussianPDFReal 0 1 (t - s)
      ≤ Real.exp 2
        * (gaussianPDFReal 0 1 (t - 2) + gaussianPDFReal 0 1 (t + 2)) := by
  have h0 : (0:ℝ) ≤ gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg 0 1 t
  have hts : t * s ≤ 2 * |t| := by
    calc t * s ≤ |t * s| := le_abs_self _
      _ = |t| * |s| := abs_mul t s
      _ ≤ |t| * 2 := mul_le_mul_of_nonneg_left hs (abs_nonneg t)
      _ = 2 * |t| := mul_comm _ _
  have h1 : gaussianPDFReal 0 1 (t - s)
      ≤ Real.exp (2 * |t|) * gaussianPDFReal 0 1 t := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg s, hts]
  have h2 : Real.exp (2 * |t|) ≤ Real.exp (2 * t) + Real.exp (-(2 * t)) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos ht, show 2 * -t = -(2 * t) by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have e1 : Real.exp (2 * t) * gaussianPDFReal 0 1 t
      = Real.exp 2 * gaussianPDFReal 0 1 (t - 2) := by
    have h := exp_mul_gaussianPDFReal_std 2 t
    norm_num at h
    exact h
  have e2 : Real.exp (-(2 * t)) * gaussianPDFReal 0 1 t
      = Real.exp 2 * gaussianPDFReal 0 1 (t + 2) := by
    have h := exp_mul_gaussianPDFReal_std (-2) t
    norm_num [sub_neg_eq_add] at h
    exact h
  calc gaussianPDFReal 0 1 (t - s)
      ≤ Real.exp (2 * |t|) * gaussianPDFReal 0 1 t := h1
    _ ≤ (Real.exp (2 * t) + Real.exp (-(2 * t))) * gaussianPDFReal 0 1 t :=
        mul_le_mul_of_nonneg_right h2 h0
    _ = Real.exp (2 * t) * gaussianPDFReal 0 1 t
        + Real.exp (-(2 * t)) * gaussianPDFReal 0 1 t := add_mul _ _ _
    _ = Real.exp 2 * gaussianPDFReal 0 1 (t - 2)
        + Real.exp 2 * gaussianPDFReal 0 1 (t + 2) := by rw [e1, e2]
    _ = Real.exp 2
        * (gaussianPDFReal 0 1 (t - 2) + gaussianPDFReal 0 1 (t + 2)) :=
        (mul_add _ _ _).symm

/-- The locally-uniform majorant for the eq.-(2.3) derivative kernel: for
`|x − x₀| ≤ 1`,
`|y − x|·ϱ(y − x) ≤ 2e^{5/2}·(ϱ(y − x₀ − 2) + ϱ(y − x₀ + 2))`. -/
lemma abs_sub_mul_gaussianPDFReal_std_le {x₀ x : ℝ} (hx : |x - x₀| ≤ 1)
    (y : ℝ) :
    |y - x| * gaussianPDFReal 0 1 (y - x)
      ≤ 2 * Real.exp (5/2 : ℝ)
        * (gaussianPDFReal 0 1 (y - x₀ - 2)
          + gaussianPDFReal 0 1 (y - x₀ + 2)) := by
  have hxx := abs_le.1 hx
  have h1 : gaussianPDFReal 0 1 (y - x - 1)
      ≤ Real.exp 2 * (gaussianPDFReal 0 1 (y - x₀ - 2)
        + gaussianPDFReal 0 1 (y - x₀ + 2)) := by
    have hs : |x - x₀ + 1| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h := gaussianPDFReal_std_shift_le hs (y - x₀)
    rw [show y - x₀ - (x - x₀ + 1) = y - x - 1 by ring] at h
    exact h
  have h2 : gaussianPDFReal 0 1 (y - x + 1)
      ≤ Real.exp 2 * (gaussianPDFReal 0 1 (y - x₀ - 2)
        + gaussianPDFReal 0 1 (y - x₀ + 2)) := by
    have hs : |x - x₀ - 1| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h := gaussianPDFReal_std_shift_le hs (y - x₀)
    rw [show y - x₀ - (x - x₀ - 1) = y - x + 1 by ring] at h
    exact h
  calc |y - x| * gaussianPDFReal 0 1 (y - x)
      ≤ Real.exp (1/2 : ℝ) * (gaussianPDFReal 0 1 (y - x - 1)
        + gaussianPDFReal 0 1 (y - x + 1)) :=
        abs_mul_gaussianPDFReal_std_le (y - x)
    _ ≤ Real.exp (1/2 : ℝ) * (2 * (Real.exp 2
        * (gaussianPDFReal 0 1 (y - x₀ - 2)
          + gaussianPDFReal 0 1 (y - x₀ + 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := add_le_add h1 h2
        linarith
    _ = 2 * Real.exp (5/2 : ℝ)
        * (gaussianPDFReal 0 1 (y - x₀ - 2)
          + gaussianPDFReal 0 1 (y - x₀ + 2)) := by
        rw [show (5/2 : ℝ) = 1/2 + 2 by norm_num, Real.exp_add]
        ring

/-! ## eq. (2.2): the convolution form of `F` -/

/-- v4 eq. (2.2) (v3 eq. (4)): `F(x) = ∫ P(y)·ϱ(y − x) dy` (Lebesgue
convolution form of the Gaussian smoothing). -/
theorem gaussianSmoothing_eq_convolution {φ : ℝ → ℝ} (hφ : Measurable φ)
    (x : ℝ) :
    gaussianSmoothing φ x
      = ∫ y, inverseRegression φ y * stdNormalPDF (y - x) := by
  rw [gaussianSmoothing,
    integral_comp_add_gaussianReal one_ne_zero x
      (lemma21_continuous hφ).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)

/-! ## eq. (2.3): differentiability of `F` -/

/-- The dominated-differentiation core for node R2: at every `x₀`, the
eq.-(2.3) kernel is integrable and `x ↦ ∫ P(y)ϱ(y − x) dy` differentiates
under the integral. -/
private lemma hasDerivAt_core {φ : ℝ → ℝ} (hφ : Measurable φ) (x₀ : ℝ) :
    Integrable (fun y => inverseRegression φ y
      * ((y - x₀) * gaussianPDFReal 0 1 (y - x₀))) (volume : Measure ℝ)
    ∧ HasDerivAt
        (fun x => ∫ y, inverseRegression φ y * gaussianPDFReal 0 1 (y - x))
        (∫ y, inverseRegression φ y
          * ((y - x₀) * gaussianPDFReal 0 1 (y - x₀))) x₀ := by
  have hP : Continuous (inverseRegression φ) := lemma21_continuous hφ
  -- the majorant, integrable by R1 at `x₀ ± 2`
  have habs : ∀ a : ℝ, Integrable
      (fun y => |inverseRegression φ y| * gaussianPDFReal 0 1 (y - a))
      (volume : Measure ℝ) := by
    intro a
    refine (lemma23_integrable hφ a).abs.congr (ae_of_all _ fun y => ?_)
    beta_reduce
    rw [abs_mul, stdNormalPDF,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 (y - a))]
  have hbint : Integrable (fun y => 2 * Real.exp (5/2 : ℝ)
      * (|inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ + 2))
        + |inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ - 2))))
      (volume : Measure ℝ) :=
    ((habs (x₀ + 2)).add (habs (x₀ - 2))).const_mul _
  have hFmeas : ∀ x : ℝ, AEStronglyMeasurable
      (fun y => inverseRegression φ y * gaussianPDFReal 0 1 (y - x))
      (volume : Measure ℝ) :=
    fun x => (hP.mul ((continuous_gaussianPDFReal 0 1).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable
  have hFint : Integrable
      (fun y => inverseRegression φ y * gaussianPDFReal 0 1 (y - x₀))
      (volume : Measure ℝ) := by
    refine (lemma23_integrable hφ x₀).congr (ae_of_all _ fun y => ?_)
    rw [stdNormalPDF]
  have hF'meas : AEStronglyMeasurable
      (fun y => inverseRegression φ y
        * ((y - x₀) * gaussianPDFReal 0 1 (y - x₀))) (volume : Measure ℝ) :=
    (hP.mul ((continuous_id.sub continuous_const).mul
      ((continuous_gaussianPDFReal 0 1).comp
        (continuous_id.sub continuous_const)))).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂(volume : Measure ℝ), ∀ x ∈ Metric.ball x₀ 1,
      ‖inverseRegression φ y * ((y - x) * gaussianPDFReal 0 1 (y - x))‖
        ≤ 2 * Real.exp (5/2 : ℝ)
          * (|inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ + 2))
            + |inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ - 2))) := by
    refine ae_of_all _ fun y x hx => ?_
    have hx1 : |x - x₀| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      exact hx.le
    have hmaj := abs_sub_mul_gaussianPDFReal_std_le hx1 y
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 (y - x))]
    calc |inverseRegression φ y| * (|y - x| * gaussianPDFReal 0 1 (y - x))
        ≤ |inverseRegression φ y| * (2 * Real.exp (5/2 : ℝ)
          * (gaussianPDFReal 0 1 (y - x₀ - 2)
            + gaussianPDFReal 0 1 (y - x₀ + 2))) :=
          mul_le_mul_of_nonneg_left hmaj (abs_nonneg _)
      _ = 2 * Real.exp (5/2 : ℝ)
          * (|inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ + 2))
            + |inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ - 2))) := by
          rw [show y - (x₀ + 2) = y - x₀ - 2 by ring,
            show y - (x₀ - 2) = y - x₀ + 2 by ring]
          ring
  have h_diff : ∀ᵐ y ∂(volume : Measure ℝ), ∀ x ∈ Metric.ball x₀ 1,
      HasDerivAt (fun x => inverseRegression φ y
        * gaussianPDFReal 0 1 (y - x))
        (inverseRegression φ y
          * ((y - x) * gaussianPDFReal 0 1 (y - x))) x := by
    refine ae_of_all _ fun y x _ => ?_
    have h1 : HasDerivAt (fun x : ℝ => y - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub y
    have h2 := (hasDerivAt_gaussianPDFReal_std (y - x)).comp x h1
    have h3 : HasDerivAt (fun x => gaussianPDFReal 0 1 (y - x))
        ((y - x) * gaussianPDFReal 0 1 (y - x)) x := by
      have heq : -(y - x) * gaussianPDFReal 0 1 (y - x) * (-1)
          = (y - x) * gaussianPDFReal 0 1 (y - x) := by ring
      rw [← heq]
      exact h2
    exact h3.const_mul (inverseRegression φ y)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => hFmeas x) hFint hF'meas h_bound hbint
    h_diff

/-- Node R2 (integrability leg): the eq.-(2.3) derivative kernel
`y ↦ P(y)·(y − x)·ϱ(y − x)` is Lebesgue-integrable for every `x`. -/
theorem integrable_gaussianSmoothing_deriv_kernel {φ : ℝ → ℝ}
    (hφ : Measurable φ) (x : ℝ) :
    Integrable (fun y => inverseRegression φ y
      * ((y - x) * stdNormalPDF (y - x))) (volume : Measure ℝ) := by
  simpa only [stdNormalPDF] using (hasDerivAt_core hφ x).1

/-- **Node R2, differentiability** (v4 Lemma 2.3, eq. (2.3), first form):
`F` is differentiable with `F′(x) = ∫ P(y)·(y − x)·ϱ(y − x) dy`. -/
theorem hasDerivAt_gaussianSmoothing {φ : ℝ → ℝ} (hφ : Measurable φ)
    (x₀ : ℝ) :
    HasDerivAt (gaussianSmoothing φ)
      (∫ y, inverseRegression φ y * ((y - x₀) * stdNormalPDF (y - x₀)))
      x₀ := by
  have hFeq : (fun x => ∫ y, inverseRegression φ y
      * gaussianPDFReal 0 1 (y - x)) = gaussianSmoothing φ := by
    funext x
    rw [gaussianSmoothing_eq_convolution hφ x]
    simp only [stdNormalPDF]
  have h := (hasDerivAt_core hφ x₀).2
  rw [hFeq] at h
  simpa only [stdNormalPDF] using h

/-- eq. (2.3), second (probabilistic) form — untagged in v4, which tags
only the first line of the display:
`F′(x) = ∫ u·P(x + u)·ϱ(u) du = E[U·P(x + U)]` (true for every `φ` — the
identity is pure translation invariance). -/
theorem deriv_gaussianSmoothing_eq_prob (φ : ℝ → ℝ) (x : ℝ) :
    ∫ y, inverseRegression φ y * ((y - x) * stdNormalPDF (y - x))
      = ∫ u, u * inverseRegression φ (x + u) ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
    (fun y => inverseRegression φ y
      * ((y - x) * stdNormalPDF (y - x))) x
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  beta_reduce
  rw [show x + u - x = u by ring, stdNormalPDF, smul_eq_mul]
  ring

/-- The eq.-(2.3) derivative is continuous (with `hasDerivAt_gaussianSmoothing`
this is `F ∈ C¹`, completing node R2). -/
theorem continuous_gaussianSmoothing_deriv {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Continuous fun x =>
      ∫ y, inverseRegression φ y * ((y - x) * stdNormalPDF (y - x)) := by
  have hP : Continuous (inverseRegression φ) := lemma21_continuous hφ
  rw [continuous_iff_continuousAt]
  intro x₀
  simp only [stdNormalPDF]
  have habs : ∀ a : ℝ, Integrable
      (fun y => |inverseRegression φ y| * gaussianPDFReal 0 1 (y - a))
      (volume : Measure ℝ) := by
    intro a
    refine (lemma23_integrable hφ a).abs.congr (ae_of_all _ fun y => ?_)
    beta_reduce
    rw [abs_mul, stdNormalPDF,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 (y - a))]
  refine continuousAt_of_dominated
    (Eventually.of_forall fun x =>
      (hP.mul ((continuous_id.sub continuous_const).mul
        ((continuous_gaussianPDFReal 0 1).comp
          (continuous_id.sub continuous_const)))).aestronglyMeasurable)
    ?_ (((habs (x₀ + 2)).add (habs (x₀ - 2))).const_mul
      (2 * Real.exp (5/2 : ℝ))) ?_
  · refine eventually_of_mem (Metric.ball_mem_nhds x₀ one_pos)
      fun x hx => ae_of_all _ fun y => ?_
    have hx1 : |x - x₀| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      exact hx.le
    have hmaj := abs_sub_mul_gaussianPDFReal_std_le hx1 y
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 (y - x))]
    calc |inverseRegression φ y| * (|y - x| * gaussianPDFReal 0 1 (y - x))
        ≤ |inverseRegression φ y| * (2 * Real.exp (5/2 : ℝ)
          * (gaussianPDFReal 0 1 (y - x₀ - 2)
            + gaussianPDFReal 0 1 (y - x₀ + 2))) :=
          mul_le_mul_of_nonneg_left hmaj (abs_nonneg _)
      _ = 2 * Real.exp (5/2 : ℝ)
          * (|inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ + 2))
            + |inverseRegression φ y| * gaussianPDFReal 0 1 (y - (x₀ - 2))) := by
          rw [show y - (x₀ + 2) = y - x₀ - 2 by ring,
            show y - (x₀ - 2) = y - x₀ + 2 by ring]
          ring
  · refine ae_of_all _ fun y => ?_
    have hc : Continuous fun x => inverseRegression φ y
        * ((y - x) * gaussianPDFReal 0 1 (y - x)) :=
      continuous_const.mul ((continuous_const.sub continuous_id).mul
        ((continuous_gaussianPDFReal 0 1).comp
          (continuous_const.sub continuous_id)))
    exact hc.continuousAt

/-- `deriv` form of eq. (2.3). -/
theorem deriv_gaussianSmoothing {φ : ℝ → ℝ} (hφ : Measurable φ) (x : ℝ) :
    deriv (gaussianSmoothing φ) x
      = ∫ y, inverseRegression φ y * ((y - x) * stdNormalPDF (y - x)) :=
  (hasDerivAt_gaussianSmoothing hφ x).deriv

/-- `F ∈ C¹` in `deriv` packaging: the derivative function of the Gaussian
smoothing is continuous. -/
theorem continuous_deriv_gaussianSmoothing {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    Continuous (deriv (gaussianSmoothing φ)) := by
  have h : deriv (gaussianSmoothing φ) = fun x =>
      ∫ y, inverseRegression φ y * ((y - x) * stdNormalPDF (y - x)) :=
    funext fun x => deriv_gaussianSmoothing hφ x
  rw [h]
  exact continuous_gaussianSmoothing_deriv hφ

end KyleUniqueness
