/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Monotone

/-!
# The Stein pipeline (blueprint nodes I1–I3; **v3** Lemma 2.5, **v3** eq. (7))

Paper of record for the development: Monteiro & Tourky, *The one-period Kyle
model has one equilibrium* (arXiv:2607.23585, **v4** of 2026-08-20). Every
other module in this tree is keyed to v4; **this one deliberately is not**,
and the reason is the single largest divergence between the artifact and the
paper's current text, so it is stated here in full.

## ⚠ This module formalizes a lemma that **v4 deleted**

What is proved below is the **one-sided Gaussian (Stein-type) inequality of
arXiv:2607.23585 v3, Lemma 2.5 (v3 §2.5, "A one-sided Gaussian
inequality"), whose outer form is v3 eq. (7)**:

`1 ≤ √(E[f(Z)²] · E[1/f′(Z)²])`  for monotone `f` with a.e. `f′ > 0`.

**v4 removed that lemma.** It has no v4 counterpart and no v4 number. In its
place v4 states a *different* lemma — v4 **Lemma 2.7**, Cacoullos's lower
Gaussian variance bound `(E[f′(V)])² ≤ Var f(V)` for bounded Lipschitz `f` —
and rebuilds the `Γ ≥ 1/2` step of its Proposition 6.1 around truncation plus
two Cauchy–Schwarz chains. The two statements are not the same inequality, so
**re-keying this file to "v4 Lemma 2.7" would be false**, and the v4 slot
numbered 2.5 is occupied by a different result again (the monotonicity lemma,
v3's Lemma 4.1). "Stein" survives in v4 only as a bibliography entry.

## Why the file stays: it is OUR route, not the paper's (Lane-C decision D7)

`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision **D7**, elects to close
the step `1 ≤ 2Γ` (blueprint node J1) with the banked v3 inequality
`one_le_sqrt_integral_sq_mul_integral_inv_sq` applied to the signed root,
rather than to formalize v4's Cacoullos route. Consequences that any
downstream claim, abstract or announcement must carry:

* the formalized proof of **v4 Proposition 6.1** is **v3's proof**, not v4's;
* this module is **our own lemma**, not "the paper's Lemma 2.5" — under v4
  that phrase names a different result, so the older citation is not stale,
  it is wrong;
* nothing here may be described as formalized content of arXiv:2607.23585v4.

The consumer is `KyleUniqueness.SignedRoot`
(`one_le_two_mul_noiseTraderLoss`), whose docstrings record the same
deviation. Crosswalk: `STATEMENT_NOTES.md` §1; the final
audit records it as faithfulness item **F1**.

All "Lemma 2.5" and "eq. (7)" references in this file are **v3** numbers and
are marked as such.

Mathlib-only file (zero project imports — the premier upstream candidate of
the campaign, blueprint hard block 2). Three layers:

* **I1 — Stieltjes–Gaussian integration by parts**
  (`integral_gaussianPDFReal_stieltjesMeasure`,
  `integral_gaussianPDFReal_stieltjesMeasure_of_monotone`): for a bounded
  monotone `f` with Stieltjes measure `μ_f`,
  `∫ ϱ dμ_f = E[Z f(Z)]`, `Z ~ N(0,1)` — proved by the layer-cake/Tonelli
  route (no BV library), with the Gaussian tail FTC
  `∫_{z>t} z ϱ(z) dz = ϱ(t)` on both tails.
* **I2 — monotone-Stieltjes domination**
  (`ae_indicator_ofReal_deriv_le_rnDeriv`,
  `lintegral_indicator_ofReal_deriv_mul_le`, `lintegral_ofReal_deriv_mul_le`):
  the a.e. derivative of a monotone function is the Radon–Nikodym derivative
  of its Stieltjes measure (`Monotone.ae_hasDerivAt`), and the
  absolutely-continuous part is dominated by the whole measure
  (`withDensity_rnDeriv_le`) — the singular part is what the paper's BV
  citation discards.
* **I3 — the Stein-type inequality** (v3 Lemma 2.5; no v4 counterpart): for
  monotone `f` with
  a.e. derivative `f' > 0`,
  `1 ≤ E[f(Z)²] · E[1/f'(Z)²]`
  (`one_le_lintegral_sq_mul_lintegral_inv_sq` in `ℝ≥0∞` with no
  integrability hypotheses; Bochner forms
  `one_le_integral_sq_mul_integral_inv_sq`,
  `one_le_sqrt_integral_sq_mul_integral_inv_sq` under `L²` hypotheses —
  the outer form of v3 eq. (7)). Proof: truncate `f` at `±N`; on
  `{|f| < N}` the truncation has the same derivative; chain
  `γ{|f|<N} ≤ (∫ f'·1)^½·(∫ 1/f')^½` (Cauchy–Schwarz),
  `∫_{|f|<N} f' dγ ≤ ∫ ϱ dμ_{f_N} = E[Z f_N(Z)] ≤ √E[f_N²] ≤ √E[f²]`
  (I2, I1, Cauchy–Schwarz, `E[Z²] = 1`), `∫ 1/f' dγ ≤ √E[1/f'²]`
  (Cauchy–Schwarz), and let `N → ∞` (continuity of measures).

The tiny Gaussian toolkit (density derivative, tail FTC, first/second
moments) is duplicated privately from `GaussianHelpers.lean` to keep this
file free of project imports.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal Topology

namespace KyleUniqueness

/-! ## Private Gaussian toolkit (duplicated from `GaussianHelpers.lean` for
self-containedness; both tails of the FTC are needed here) -/

private lemma pdf_hasDerivAt' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  have hv0 : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hsub : HasDerivAt (fun y : ℝ => y - μ) 1 x := (hasDerivAt_id x).sub_const μ
  have hchain := ((((hasDerivAt_pow 2 (x - μ)).comp x hsub).neg.div_const
    (2 * (v : ℝ))).exp).const_mul ((√(2 * π * (v : ℝ)))⁻¹)
  convert hchain using 1
  · rfl
  · rfl
  · funext y
    simp only [Function.comp_apply, Pi.neg_apply]
    rw [gaussianPDFReal]
  · simp only [Function.comp_apply, Pi.neg_apply, Nat.cast_ofNat, mul_one]
    rw [gaussianPDFReal]
    field_simp
    ring

private lemma pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  simpa using pdf_hasDerivAt' 0 one_ne_zero x

private lemma pdf_tendsto_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => (y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num)
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-0 : ℝ) tendsto_id))
  have h2 : Tendsto (fun y : ℝ => -(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) atTop atBot := by
    simp only [neg_div]
    exact tendsto_neg_atBot_iff.mpr h1
  have h3 := Real.tendsto_exp_atBot.comp h2
  have h4 := h3.const_mul ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹)
  simpa [gaussianPDFReal_def, Function.comp_def, sub_eq_add_neg] using h4

private lemma pdf_neg (x : ℝ) :
    gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDFReal]

private lemma pdf_tendsto_atBot :
    Tendsto (gaussianPDFReal 0 1) atBot (𝓝 0) := by
  have h := pdf_tendsto_atTop.comp tendsto_neg_atBot_atTop
  have heq : (gaussianPDFReal 0 1 ∘ fun y : ℝ => -y) = gaussianPDFReal 0 1 := by
    funext y; simp [Function.comp_apply, pdf_neg]
  rwa [heq] at h

private lemma integrable_id_gaussian :
    Integrable id (gaussianReal 0 1) :=
  memLp_one_iff_integrable.mp (by simpa using memLp_id_gaussianReal (μ := 0) (v := 1) 1)

private lemma integrable_id_mul_pdf :
    Integrable (fun x => x * gaussianPDFReal 0 1 x) := by
  have h : Integrable id (gaussianReal 0 1) := integrable_id_gaussian
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  have heq : ∀ x, (gaussianPDF 0 1 x).toReal • id x = x * gaussianPDFReal 0 1 x := by
    intro x
    simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x),
      smul_eq_mul, mul_comm]
  exact h.congr (ae_of_all _ fun x => heq x)

/-- Right tail FTC: `∫_{(t,∞)} z·ϱ(z) dz = ϱ(t)`. -/
private lemma integral_Ioi_tail (a : ℝ) :
    ∫ x in Ioi a, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 a := by
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt (fun y => -gaussianPDFReal 0 1 y)
        (x * gaussianPDFReal 0 1 x) x := by
    intro x _
    have h := (pdf_hasDerivAt x).neg
    rwa [neg_mul, neg_neg] at h
  have hint : IntegrableOn (fun x => x * gaussianPDFReal 0 1 x) (Ioi a) :=
    integrable_id_mul_pdf.integrableOn
  have htend : Tendsto (fun y => -gaussianPDFReal 0 1 y) atTop (𝓝 0) := by
    simpa using pdf_tendsto_atTop.neg
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  simpa using this

/-- Left tail FTC: `∫_{(-∞,t)} (−z)·ϱ(z) dz = ϱ(t)`. -/
private lemma integral_Iio_tail (a : ℝ) :
    ∫ x in Iio a, -x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 a := by
  have hderiv : ∀ x ∈ Iic a,
      HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x :=
    fun x _ => pdf_hasDerivAt x
  have hint : IntegrableOn (fun x => -x * gaussianPDFReal 0 1 x) (Iic a) := by
    have := integrable_id_mul_pdf.neg.integrableOn (s := Iic a)
    simpa [neg_mul] using this
  have := integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint pdf_tendsto_atBot
  rw [show ∫ x in Iio a, -x * gaussianPDFReal 0 1 x
      = ∫ x in Iic a, -x * gaussianPDFReal 0 1 x from
    setIntegral_congr_set Iio_ae_eq_Iic]
  simpa using this

/-- Second moment of the standard normal: `E[Z²] = 1`. -/
private lemma integral_sq_gaussian :
    ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have hL2 : MemLp id 2 (gaussianReal 0 1) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := 1) 2
  have h := variance_eq_sub (μ := gaussianReal 0 1) (X := id) hL2
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id_eq] at h
  rw [integral_id_gaussianReal] at h
  norm_num at h
  linarith [h]

/-- The standard normal density is bounded by `(√(2π))⁻¹`. -/
private lemma pdf_le_bound (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (√(2 * π))⁻¹ := by
  rw [gaussianPDFReal]
  have h1 : rexp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div]
    exact neg_nonpos_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
  calc (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * rexp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
      ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * 1 := by
        refine mul_le_mul_of_nonneg_left h1 ?_
        positivity
    _ = (√(2 * π))⁻¹ := by norm_num

/-! ## I1 — Stieltjes–Gaussian integration by parts (layer-cake route) -/

/-- **I1, Stieltjes form.** For a bounded Stieltjes function `s` with measure
`μ_s`, `∫ ϱ dμ_s = E[Z·s(Z)]` where `Z ~ N(0,1)` and `ϱ` is the standard
normal density. This is the Gaussian integration-by-parts identity for
monotone right-continuous integrands (the engine of v3 Lemma 2.5, which v4
deleted; upstream candidate on its own merits). -/
theorem integral_gaussianPDFReal_stieltjesMeasure (s : StieltjesFunction ℝ)
    {C : ℝ} (hbd : ∀ x, |s x| ≤ C) :
    ∫ t, gaussianPDFReal 0 1 t ∂s.measure = ∫ z, z * s z ∂gaussianReal 0 1 := by
  haveI : IsFiniteMeasure s.measure := s.isFiniteMeasure_of_forall_abs_le hbd
  set γ := gaussianReal 0 1 with hγ
  set m := s.measure with hm
  -- integrability of both sides
  have hs_meas : Measurable s := s.mono.measurable
  have hint : Integrable (fun z => z * s z) γ := by
    refine Integrable.mono' (integrable_id_gaussian.abs.const_mul C)
      ((measurable_id.mul hs_meas).aestronglyMeasurable) ?_
    refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |z| * |s z| ≤ |z| * C := by
          refine mul_le_mul_of_nonneg_left (hbd z) (abs_nonneg z)
      _ = C * |id z| := by rw [mul_comm]; rfl
  have hint0 : Integrable (fun z => z * s 0) γ :=
    integrable_id_gaussian.mul_const (s 0)
  have hintc : Integrable (fun z => z * (s z - s 0)) γ := by
    have : (fun z => z * (s z - s 0)) = fun z => z * s z - z * s 0 := by
      funext z; ring
    rw [this]; exact hint.sub hint0
  have hϱint : Integrable (fun t => gaussianPDFReal 0 1 t) m := by
    refine memLp_one_iff_integrable.mp ?_
    refine MemLp.of_bound ((measurable_gaussianPDFReal 0 1).aestronglyMeasurable)
      ((√(2 * π))⁻¹) (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
    exact pdf_le_bound t
  -- center the RHS
  have hcenter : ∫ z, z * s z ∂γ = ∫ z, z * (s z - s 0) ∂γ := by
    have hsplit : ∫ z, z * (s z - s 0) ∂γ
        = (∫ z, z * s z ∂γ) - ∫ z, z * s 0 ∂γ := by
      have : (fun z => z * (s z - s 0)) = fun z => z * s z - z * s 0 := by
        funext z; ring
      rw [this]; exact integral_sub hint hint0
    have hzero : ∫ z, z * s 0 ∂γ = 0 := by
      rw [integral_mul_const]
      have h0 : ∫ z, z ∂γ = 0 := by
        rw [hγ]; exact integral_id_gaussianReal
      rw [h0, zero_mul]
    rw [hsplit, hzero, sub_zero]
  rw [hcenter]
  -- split both sides at 0
  rw [← integral_add_compl (measurableSet_Ioi (a := (0:ℝ))) hintc,
    ← integral_add_compl (measurableSet_Ioi (a := (0:ℝ))) hϱint, compl_Ioi]
  have hγwd : γ = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero _ one_ne_zero
  -- ===== positive piece =====
  have hpos : ∫ z in Ioi (0:ℝ), z * (s z - s 0) ∂γ
      = ∫ t in Ioi (0:ℝ), gaussianPDFReal 0 1 t ∂m := by
    -- to lintegral
    have hnnA : 0 ≤ᵐ[γ.restrict (Ioi 0)] fun z => z * (s z - s 0) := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with z hz
      exact mul_nonneg (le_of_lt hz) (sub_nonneg.2 (s.mono (le_of_lt hz)))
    have hmeasA : AEStronglyMeasurable (fun z => z * (s z - s 0))
        (γ.restrict (Ioi 0)) :=
      ((measurable_id.mul (hs_meas.sub measurable_const))).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hnnA hmeasA]
    -- rewrite the integrand as ofReal z * m (Ioc 0 z)
    have hcong : ∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal (z * (s z - s 0)) ∂γ
        = ∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal z * m (Ioc 0 z) ∂γ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with z hz
      rw [ENNReal.ofReal_mul (le_of_lt hz), s.measure_Ioc]
    rw [hcong]
    -- expand the measure as an inner lintegral and swap
    have hIoc_ind : ∀ z : ℝ, m (Ioc 0 z)
        = ∫⁻ t, {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
            (fun _ => (1:ℝ≥0∞)) (z, t) ∂m := by
      intro z
      rw [← lintegral_indicator_one measurableSet_Ioc]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Ioc 0 z
      · rw [indicator_of_mem ht, indicator_of_mem
          (show (z, t) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} from ⟨ht.1, ht.2⟩)]
        rfl
      · rw [indicator_of_notMem ht, indicator_of_notMem
          (fun hmem => ht ⟨hmem.1, hmem.2⟩)]
    have hDmeas : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    have hswap : ∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal z * m (Ioc 0 z) ∂γ
        = ∫⁻ t, ∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal z
            * {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t) ∂γ ∂m := by
      have h1 : ∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal z * m (Ioc 0 z) ∂γ
          = ∫⁻ z in Ioi (0:ℝ), ∫⁻ t, ENNReal.ofReal z
              * {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
                  (fun _ => (1:ℝ≥0∞)) (z, t) ∂m ∂γ := by
        refine lintegral_congr fun z => ?_
        rw [hIoc_ind z, ← lintegral_const_mul (ENNReal.ofReal z)]
        exact (measurable_const.indicator hDmeas).comp
          (measurable_prodMk_left (x := z))
      rw [h1]
      refine lintegral_lintegral_swap ?_
      refine Measurable.aemeasurable ?_
      exact ((ENNReal.measurable_ofReal.comp measurable_fst)).mul
        (measurable_const.indicator hDmeas)
    rw [hswap]
    -- compute the inner z-integral
    have hinner : ∀ t : ℝ,
        ∫⁻ z in Ioi (0:ℝ), ENNReal.ofReal z
            * {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t) ∂γ
        = (Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal (gaussianPDFReal 0 1 t)) t := by
      intro t
      by_cases ht : (0:ℝ) < t
      · -- integrand = (Ici t).indicator (ofReal ·)
        have hind : ∀ z : ℝ, ENNReal.ofReal z
            * {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t)
            = (Ici t).indicator (fun z => ENNReal.ofReal z) z := by
          intro z
          by_cases hz : t ≤ z
          · rw [indicator_of_mem (show z ∈ Ici t from hz),
              indicator_of_mem (show (z, t) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}
                from ⟨ht, hz⟩), mul_one]
          · rw [indicator_of_notMem (show z ∉ Ici t from hz),
              indicator_of_notMem
                (show (z, t) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}
                  from fun hmem => hz hmem.2), mul_zero]
        rw [lintegral_congr fun z => hind z, lintegral_indicator measurableSet_Ici,
          Measure.restrict_restrict measurableSet_Ici,
          inter_eq_self_of_subset_left
            (show Ici t ⊆ Ioi (0:ℝ) from fun z hz => lt_of_lt_of_le ht hz),
          indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]
        -- ∫⁻ z in Ici t, ofReal z ∂γ = ofReal (ϱ t)
        rw [hγwd, restrict_withDensity measurableSet_Ici,
          lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
            ENNReal.measurable_ofReal]
        have hcong2 : ∫⁻ z in Ici t, (gaussianPDF 0 1 * fun z => ENNReal.ofReal z) z ∂volume
            = ∫⁻ z in Ici t, ENNReal.ofReal (z * gaussianPDFReal 0 1 z) ∂volume := by
          refine lintegral_congr fun z => ?_
          simp only [Pi.mul_apply, gaussianPDF]
          rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 z), mul_comm]
        rw [hcong2, ← ofReal_integral_eq_lintegral_ofReal
          (integrable_id_mul_pdf.integrableOn)
          ((ae_restrict_mem measurableSet_Ici).mono fun z hz =>
            mul_nonneg (le_trans (le_of_lt ht) hz) (gaussianPDFReal_nonneg 0 1 z))]
        rw [integral_Ici_eq_integral_Ioi, integral_Ioi_tail]
      · -- t ≤ 0 : the indicator is empty
        have hind0 : ∀ z : ℝ, ENNReal.ofReal z
            * {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t) = 0 := by
          intro z
          rw [indicator_of_notMem
            (show (z, t) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}
              from fun hmem => ht hmem.1), mul_zero]
        rw [lintegral_congr fun z => hind0 z, lintegral_zero,
          indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]
    rw [lintegral_congr fun t => hinner t, lintegral_indicator measurableSet_Ioi]
    -- back to Bochner
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun t => gaussianPDFReal_nonneg 0 1 t)
      ((measurable_gaussianPDFReal 0 1).aestronglyMeasurable)]
  -- ===== nonpositive piece =====
  have hneg : ∫ z in Iic (0:ℝ), z * (s z - s 0) ∂γ
      = ∫ t in Iic (0:ℝ), gaussianPDFReal 0 1 t ∂m := by
    have hnnB : 0 ≤ᵐ[γ.restrict (Iic 0)] fun z => z * (s z - s 0) := by
      filter_upwards [ae_restrict_mem (measurableSet_Iic (a := (0:ℝ)))] with z hz
      have h2 : (0:ℝ) ≤ (-z) * (s 0 - s z) :=
        mul_nonneg (neg_nonneg.2 hz) (sub_nonneg.2 (s.mono hz))
      have h3 : z * (s z - s 0) = (-z) * (s 0 - s z) := by ring
      rw [h3]; exact h2
    have hmeasB : AEStronglyMeasurable (fun z => z * (s z - s 0))
        (γ.restrict (Iic 0)) :=
      ((measurable_id.mul (hs_meas.sub measurable_const))).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hnnB hmeasB]
    have hcong : ∫⁻ z in Iic (0:ℝ), ENNReal.ofReal (z * (s z - s 0)) ∂γ
        = ∫⁻ z in Iic (0:ℝ), ENNReal.ofReal (-z) * m (Ioc z 0) ∂γ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem (measurableSet_Iic (a := (0:ℝ)))] with z hz
      rw [show z * (s z - s 0) = (-z) * (s 0 - s z) by ring,
        ENNReal.ofReal_mul (neg_nonneg.2 hz), s.measure_Ioc]
    rw [hcong]
    have hDmeas : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0} :=
      (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have hIoc_ind : ∀ z : ℝ, m (Ioc z 0)
        = ∫⁻ t, {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}.indicator
            (fun _ => (1:ℝ≥0∞)) (z, t) ∂m := by
      intro z
      rw [← lintegral_indicator_one measurableSet_Ioc]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Ioc z 0
      · rw [indicator_of_mem ht, indicator_of_mem
          (show (z, t) ∈ {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0} from ⟨ht.1, ht.2⟩)]
        rfl
      · rw [indicator_of_notMem ht, indicator_of_notMem
          (fun hmem => ht ⟨hmem.1, hmem.2⟩)]
    have hswap : ∫⁻ z in Iic (0:ℝ), ENNReal.ofReal (-z) * m (Ioc z 0) ∂γ
        = ∫⁻ t, ∫⁻ z in Iic (0:ℝ), ENNReal.ofReal (-z)
            * {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t) ∂γ ∂m := by
      have h1 : ∫⁻ z in Iic (0:ℝ), ENNReal.ofReal (-z) * m (Ioc z 0) ∂γ
          = ∫⁻ z in Iic (0:ℝ), ∫⁻ t, ENNReal.ofReal (-z)
              * {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}.indicator
                  (fun _ => (1:ℝ≥0∞)) (z, t) ∂m ∂γ := by
        refine lintegral_congr fun z => ?_
        rw [hIoc_ind z, ← lintegral_const_mul (ENNReal.ofReal (-z))]
        exact (measurable_const.indicator hDmeas).comp
          (measurable_prodMk_left (x := z))
      rw [h1]
      refine lintegral_lintegral_swap ?_
      refine Measurable.aemeasurable ?_
      exact ((ENNReal.measurable_ofReal.comp measurable_fst.neg)).mul
        (measurable_const.indicator hDmeas)
    rw [hswap]
    have hinner : ∀ t : ℝ,
        ∫⁻ z in Iic (0:ℝ), ENNReal.ofReal (-z)
            * {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t) ∂γ
        = (Iic (0:ℝ)).indicator (fun t => ENNReal.ofReal (gaussianPDFReal 0 1 t)) t := by
      intro t
      by_cases ht : t ≤ (0:ℝ)
      · have hind : ∀ z : ℝ, ENNReal.ofReal (-z)
            * {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t)
            = (Iio t).indicator (fun z => ENNReal.ofReal (-z)) z := by
          intro z
          by_cases hz : z < t
          · rw [indicator_of_mem (show z ∈ Iio t from hz),
              indicator_of_mem (show (z, t) ∈ {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}
                from ⟨hz, ht⟩), mul_one]
          · rw [indicator_of_notMem (show z ∉ Iio t from hz),
              indicator_of_notMem
                (show (z, t) ∉ {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}
                  from fun hmem => hz hmem.1), mul_zero]
        rw [lintegral_congr fun z => hind z, lintegral_indicator measurableSet_Iio,
          Measure.restrict_restrict measurableSet_Iio,
          inter_eq_self_of_subset_left
            (show Iio t ⊆ Iic (0:ℝ) from fun z hz => le_of_lt (lt_of_lt_of_le hz ht)),
          indicator_of_mem (show t ∈ Iic (0:ℝ) from ht)]
        rw [hγwd, restrict_withDensity measurableSet_Iio,
          lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
            (show Measurable fun z : ℝ => ENNReal.ofReal (-z) from
              ENNReal.measurable_ofReal.comp measurable_neg)]
        have hcong2 : ∫⁻ z in Iio t,
            (gaussianPDF 0 1 * fun z => ENNReal.ofReal (-z)) z ∂volume
            = ∫⁻ z in Iio t, ENNReal.ofReal (-z * gaussianPDFReal 0 1 z) ∂volume := by
          refine lintegral_congr fun z => ?_
          simp only [Pi.mul_apply, gaussianPDF]
          rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 z), mul_comm]
        rw [hcong2, ← ofReal_integral_eq_lintegral_ofReal
          ((integrable_id_mul_pdf.neg.congr (ae_of_all _ fun z => by
            simp [neg_mul])).integrableOn)
          ((ae_restrict_mem measurableSet_Iio).mono fun z hz =>
            mul_nonneg (neg_nonneg.2 (le_of_lt (lt_of_lt_of_le hz ht)))
              (gaussianPDFReal_nonneg 0 1 z))]
        rw [integral_Iio_tail]
      · have hind0 : ∀ z : ℝ, ENNReal.ofReal (-z)
            * {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}.indicator
                (fun _ => (1:ℝ≥0∞)) (z, t) = 0 := by
          intro z
          rw [indicator_of_notMem
            (show (z, t) ∉ {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0}
              from fun hmem => ht hmem.2), mul_zero]
        rw [lintegral_congr fun z => hind0 z, lintegral_zero,
          indicator_of_notMem (show t ∉ Iic (0:ℝ) from ht)]
    rw [lintegral_congr fun t => hinner t, lintegral_indicator measurableSet_Iic]
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun t => gaussianPDFReal_nonneg 0 1 t)
      ((measurable_gaussianPDFReal 0 1).aestronglyMeasurable)]
  rw [hpos, hneg]

/-- The right-continuous modification of a bounded monotone function obeys
the same bound. -/
private lemma abs_stieltjesFunction_le {f : ℝ → ℝ} (hf : Monotone f) {C : ℝ}
    (hbd : ∀ x, |f x| ≤ C) (x : ℝ) : |hf.stieltjesFunction x| ≤ C := by
  rw [hf.stieltjesFunction_eq]
  refine abs_le.2 ⟨?_, ?_⟩
  · exact le_trans (abs_le.1 (hbd x)).1 (hf.le_rightLim le_rfl)
  · exact le_trans (hf.rightLim_le (lt_add_one x)) (abs_le.1 (hbd (x + 1))).2

/-- **I1, monotone form.** For a bounded monotone `f`,
`∫ ϱ dμ_f = E[Z f(Z)]`, where `μ_f` is the Stieltjes measure of the
right-continuous modification of `f` (`Monotone.stieltjesFunction`). The
modification only moves countably many points, which are Gaussian-null. -/
theorem integral_gaussianPDFReal_stieltjesMeasure_of_monotone {f : ℝ → ℝ}
    (hf : Monotone f) {C : ℝ} (hbd : ∀ x, |f x| ≤ C) :
    ∫ t, gaussianPDFReal 0 1 t ∂hf.stieltjesFunction.measure
      = ∫ z, z * f z ∂gaussianReal 0 1 := by
  rw [integral_gaussianPDFReal_stieltjesMeasure hf.stieltjesFunction
    (abs_stieltjesFunction_le hf hbd)]
  refine integral_congr_ae ?_
  have hcount : Set.Countable {x | hf.stieltjesFunction x ≠ f x} := by
    refine Countable.mono ?_ hf.countable_not_continuousAt
    intro x hx hcont
    refine hx ?_
    rw [hf.stieltjesFunction_eq]
    exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 hcont.continuousWithinAt
  have hnull : volume {x | hf.stieltjesFunction x ≠ f x} = 0 :=
    hcount.measure_zero _
  have haev : ∀ᵐ z ∂volume, hf.stieltjesFunction z = f z := by
    rw [ae_iff]
    simpa only [ne_eq] using hnull
  have hae : ∀ᵐ z ∂gaussianReal 0 1, hf.stieltjesFunction z = f z :=
    haev.filter_mono (gaussianReal_absolutelyContinuous 0 one_ne_zero).ae_le
  filter_upwards [hae] with z hz
  rw [hz]

/-! ## I2 — monotone-Stieltjes domination -/

/-- **I2, pointwise core.** Wherever a monotone `f` has a derivative `f'`,
`ofReal (f' x)` is a.e. dominated by the Radon–Nikodym derivative of the
Stieltjes measure of `f` w.r.t. Lebesgue (the singular part of the measure
is what gets discarded). -/
theorem ae_indicator_ofReal_deriv_le_rnDeriv {f f' : ℝ → ℝ} (hf : Monotone f)
    {s : Set ℝ} (hf' : ∀ᵐ x ∂volume, x ∈ s → HasDerivAt f (f' x) x) :
    ∀ᵐ x ∂volume, s.indicator (fun y => ENNReal.ofReal (f' y)) x
      ≤ hf.stieltjesFunction.measure.rnDeriv volume x := by
  filter_upwards [hf', hf.ae_hasDerivAt] with x hx hx'
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, (hx hxs).unique hx']
    exact ENNReal.ofReal_toReal_le
  · rw [indicator_of_notMem hxs]
    exact zero_le

/-- **I2, integral form** (the monotone-Stieltjes domination): for monotone
`f` with derivative `f'` on `s` and any measurable `g : ℝ → ℝ≥0∞`,
`∫ 1ₛ·f'·g dx ≤ ∫ g dμ_f`. -/
theorem lintegral_indicator_ofReal_deriv_mul_le {f f' : ℝ → ℝ}
    (hf : Monotone f) {s : Set ℝ}
    (hf' : ∀ᵐ x ∂volume, x ∈ s → HasDerivAt f (f' x) x)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, s.indicator (fun y => ENNReal.ofReal (f' y)) x * g x ∂volume
      ≤ ∫⁻ x, g x ∂hf.stieltjesFunction.measure := by
  have h1 : ∫⁻ x, s.indicator (fun y => ENNReal.ofReal (f' y)) x * g x ∂volume
      ≤ ∫⁻ x, hf.stieltjesFunction.measure.rnDeriv volume x * g x ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_indicator_ofReal_deriv_le_rnDeriv hf hf'] with x hx
    exact mul_le_mul_left hx _
  refine h1.trans ?_
  have h2 : ∫⁻ x, hf.stieltjesFunction.measure.rnDeriv volume x * g x ∂volume
      = ∫⁻ x, g x
          ∂(volume.withDensity (hf.stieltjesFunction.measure.rnDeriv volume)) := by
    rw [lintegral_withDensity_eq_lintegral_mul volume
      (Measure.measurable_rnDeriv _ _) hg]
    rfl
  rw [h2]
  exact lintegral_mono' (Measure.withDensity_rnDeriv_le _ _) le_rfl

/-- **I2, whole-line form**: `∫ f'·g dx ≤ ∫ g dμ_f`. -/
theorem lintegral_ofReal_deriv_mul_le {f f' : ℝ → ℝ} (hf : Monotone f)
    (hf' : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ENNReal.ofReal (f' x) * g x ∂volume
      ≤ ∫⁻ x, g x ∂hf.stieltjesFunction.measure := by
  have h := lintegral_indicator_ofReal_deriv_mul_le hf (s := univ)
    (hf'.mono fun x hx _ => hx) hg
  simpa [indicator_univ] using h

/-! ## Truncation compatibility -/

/-- On `{|f| < N}`, the clamp of `f` at `±N` inherits the derivative of `f`
(a.e.): the truncation is locally equal to `f` at every point of a.e.
differentiability inside the safe zone. -/
theorem ae_hasDerivAt_clamp_of_abs_lt {f f' : ℝ → ℝ}
    (hf' : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x) (N : ℝ) :
    ∀ᵐ x ∂volume, |f x| < N →
      HasDerivAt (fun y => max (-N) (min (f y) N)) (f' x) x := by
  filter_upwards [hf'] with x hx hxN
  have hcont : ContinuousAt f x := hx.continuousAt
  have hmem : {t : ℝ | |t| < N} ∈ 𝓝 (f x) :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hxN
  have hev0 : ∀ᶠ y in 𝓝 x, |f y| < N := hcont.tendsto.eventually hmem
  have hev : (fun y => max (-N) (min (f y) N)) =ᶠ[𝓝 x] f := by
    filter_upwards [hev0] with y hy
    rw [min_eq_left (le_of_lt (abs_lt.1 hy).2),
      max_eq_right (le_of_lt (abs_lt.1 hy).1)]
  exact hev.hasDerivAt_iff.2 hx

/-! ## I3 — the Stein-type inequality (v3 Lemma 2.5; deleted in v4) -/

private lemma integrable_pdf_of_finite (m : Measure ℝ) [IsFiniteMeasure m] :
    Integrable (fun t => gaussianPDFReal 0 1 t) m := by
  refine memLp_one_iff_integrable.mp ?_
  refine MemLp.of_bound ((measurable_gaussianPDFReal 0 1).aestronglyMeasurable)
    ((√(2 * π))⁻¹) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
  exact pdf_le_bound t

/-- I3 core with a measurable derivative representative. -/
private theorem stein_core {f f' : ℝ → ℝ} (hf : Monotone f)
    (hf'meas : Measurable f')
    (hf' : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x)
    (hpos : ∀ᵐ x ∂volume, 0 < f' x) :
    1 ≤ (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂gaussianReal 0 1)
        * ∫⁻ x, ENNReal.ofReal ((f' x)⁻¹ ^ 2) ∂gaussianReal 0 1 := by
  have hγac : gaussianReal 0 1 ≪ (volume : Measure ℝ) :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hposγ : ∀ᵐ x ∂gaussianReal 0 1, 0 < f' x := hpos.filter_mono hγac.ae_le
  set A := ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂gaussianReal 0 1 with hA
  set B := ∫⁻ x, ENNReal.ofReal ((f' x)⁻¹ ^ 2) ∂gaussianReal 0 1 with hB
  -- the exhausting safe zones
  have hSmeas : ∀ N : ℕ, MeasurableSet {x : ℝ | |f x| < (N:ℝ)} := fun N =>
    measurableSet_lt (continuous_abs.measurable.comp hf.measurable)
      measurable_const
  have hSmono : Monotone fun N : ℕ => {x : ℝ | |f x| < (N:ℝ)} := by
    intro M N hMN x hx
    have hx' : |f x| < (M:ℝ) := hx
    exact lt_of_lt_of_le hx' (Nat.cast_le.2 hMN)
  have hSunion : ⋃ N : ℕ, {x : ℝ | |f x| < (N:ℝ)} = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt |f x|
    exact mem_iUnion.2 ⟨N, hN⟩
  -- the per-truncation bound
  have hkey : ∀ N : ℕ,
      gaussianReal 0 1 {x : ℝ | |f x| < (N:ℝ)} ≤ (A * B) ^ ((1:ℝ)/4) := by
    intro N
    set SN := {x : ℝ | |f x| < (N:ℝ)} with hSNdef
    set fN : ℝ → ℝ := fun y => max (-(N:ℝ)) (min (f y) (N:ℝ)) with hfNdef
    have hfNmono : Monotone fN := monotone_const.max (hf.min monotone_const)
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hfNbd : ∀ x, |fN x| ≤ (N:ℝ) := fun x =>
      abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    have hfNabs : ∀ x, |fN x| ≤ |f x| := fun x =>
      abs_le.2 ⟨le_max_of_le_right (le_min (neg_abs_le _)
          (le_trans (neg_nonpos_of_nonneg (abs_nonneg _)) hN0)),
        max_le (le_trans (neg_nonpos_of_nonneg hN0) (abs_nonneg _))
          ((min_le_left _ _).trans (le_abs_self _))⟩
    have hfN' : ∀ᵐ x ∂volume, x ∈ SN → HasDerivAt fN (f' x) x := by
      filter_upwards [ae_hasDerivAt_clamp_of_abs_lt hf' (N:ℝ)] with x hx hxS
      exact hx hxS
    -- Cauchy–Schwarz 1: γ(SN) ≤ P^{1/2}·Q^{1/2}
    set φ₁ : ℝ → ℝ≥0∞ :=
      fun x => (SN.indicator (fun y => ENNReal.ofReal (f' y)) x) ^ ((1:ℝ)/2)
      with hφ₁def
    set φ₂ : ℝ → ℝ≥0∞ := fun x => (ENNReal.ofReal ((f' x)⁻¹)) ^ ((1:ℝ)/2)
      with hφ₂def
    have hφ₁m : AEMeasurable φ₁ (gaussianReal 0 1) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        ((hf'meas.ennreal_ofReal.indicator (hSmeas N)).aemeasurable)
    have hφ₂m : AEMeasurable φ₂ (gaussianReal 0 1) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (hf'meas.inv.ennreal_ofReal.aemeasurable)
    have hCS1 := ENNReal.lintegral_mul_le_Lp_mul_Lq (gaussianReal 0 1)
      Real.HolderConjugate.two_two hφ₁m hφ₂m
    have hLHS : ∫⁻ x, (φ₁ * φ₂) x ∂gaussianReal 0 1 = gaussianReal 0 1 SN := by
      rw [← lintegral_indicator_one (hSmeas N)]
      refine lintegral_congr_ae ?_
      filter_upwards [hposγ] with x hx
      by_cases hxS : x ∈ SN
      · simp only [Pi.mul_apply, hφ₁def, hφ₂def, indicator_of_mem hxS]
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
          ← ENNReal.ofReal_mul (le_of_lt hx), mul_inv_cancel₀ (ne_of_gt hx),
          ENNReal.ofReal_one, ENNReal.one_rpow,
          indicator_of_mem (show x ∈ {x : ℝ | |f x| < (N:ℝ)} from hxS)]
        rfl
      · simp only [Pi.mul_apply, hφ₁def, hφ₂def, indicator_of_notMem hxS]
        rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2), zero_mul,
          indicator_of_notMem (show x ∉ {x : ℝ | |f x| < (N:ℝ)} from hxS)]
    have hsq₁ : ∫⁻ x, φ₁ x ^ (2:ℝ) ∂gaussianReal 0 1
        = ∫⁻ x, SN.indicator (fun y => ENNReal.ofReal (f' y)) x
            ∂gaussianReal 0 1 := by
      refine lintegral_congr fun x => ?_
      rw [hφ₁def, ← ENNReal.rpow_mul,
        show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hsq₂ : ∫⁻ x, φ₂ x ^ (2:ℝ) ∂gaussianReal 0 1
        = ∫⁻ x, ENNReal.ofReal ((f' x)⁻¹) ∂gaussianReal 0 1 := by
      refine lintegral_congr fun x => ?_
      rw [hφ₂def, ← ENNReal.rpow_mul,
        show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    -- P ≤ A^{1/2} : domination (I2) + IBP (I1) + Cauchy–Schwarz 2
    have hP2 : ∫⁻ x, SN.indicator (fun y => ENNReal.ofReal (f' y)) x
        ∂gaussianReal 0 1 ≤ A ^ ((1:ℝ)/2) := by
      have hstep : ∫⁻ x, SN.indicator (fun y => ENNReal.ofReal (f' y)) x
          ∂gaussianReal 0 1
          = ∫⁻ x, SN.indicator (fun y => ENNReal.ofReal (f' y)) x
              * gaussianPDF 0 1 x ∂volume := by
        rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
          lintegral_withDensity_eq_lintegral_mul volume
            (measurable_gaussianPDF 0 1)
            (hf'meas.ennreal_ofReal.indicator (hSmeas N))]
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, mul_comm]
      rw [hstep]
      refine le_trans (lintegral_indicator_ofReal_deriv_mul_le hfNmono hfN'
        (measurable_gaussianPDF 0 1)) ?_
      haveI hfin : IsFiniteMeasure hfNmono.stieltjesFunction.measure :=
        hfNmono.stieltjesFunction.isFiniteMeasure_of_forall_abs_le
          (abs_stieltjesFunction_le hfNmono hfNbd)
      have heq2 : ∫⁻ x, gaussianPDF 0 1 x ∂hfNmono.stieltjesFunction.measure
          = ENNReal.ofReal (∫ t, gaussianPDFReal 0 1 t
              ∂hfNmono.stieltjesFunction.measure) := by
        rw [ofReal_integral_eq_lintegral_ofReal
          (integrable_pdf_of_finite _)
          (ae_of_all _ fun t => gaussianPDFReal_nonneg 0 1 t)]
        rfl
      rw [heq2,
        integral_gaussianPDFReal_stieltjesMeasure_of_monotone hfNmono hfNbd]
      -- Cauchy–Schwarz on the Bochner side: E[Z·f_N(Z)] ≤ √E[f_N²]
      have hintZfN : Integrable (fun z => z * fN z) (gaussianReal 0 1) := by
        refine Integrable.mono' (integrable_id_gaussian.abs.const_mul (N:ℝ))
          ((measurable_id.mul hfNmono.measurable).aestronglyMeasurable)
          (ae_of_all _ fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        calc |z| * |fN z| ≤ |z| * (N:ℝ) :=
              mul_le_mul_of_nonneg_left (hfNbd z) (abs_nonneg z)
          _ = (N:ℝ) * |id z| := by rw [mul_comm]; rfl
      have hfN2int : Integrable (fun z => fN z ^ 2) (gaussianReal 0 1) := by
        refine memLp_one_iff_integrable.mp ?_
        refine MemLp.of_bound
          ((hfNmono.measurable.pow_const 2).aestronglyMeasurable)
          ((N:ℝ) ^ 2) (ae_of_all _ fun z => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.1 (hfNbd z)).1])
          (abs_le.1 (hfNbd z)).2
      have hCS2 : ∫ z, z * fN z ∂gaussianReal 0 1
          ≤ (∫ z, fN z ^ 2 ∂gaussianReal 0 1) ^ ((1:ℝ)/2) := by
        have hidL2 : MemLp (fun z : ℝ => |z|) (ENNReal.ofReal 2)
            (gaussianReal 0 1) := by
          rw [ENNReal.ofReal_ofNat]
          have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).norm
          have h2 : ((2:ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_cast
          rw [h2] at h
          exact h
        have hfNL2 : MemLp (fun z : ℝ => |fN z|) (ENNReal.ofReal 2)
            (gaussianReal 0 1) := by
          refine MemLp.of_bound
            ((continuous_abs.measurable.comp
              hfNmono.measurable).aestronglyMeasurable) ((N:ℝ))
            (ae_of_all _ fun z => ?_)
          rw [Real.norm_eq_abs, abs_abs]
          exact hfNbd z
        have hHold := integral_mul_le_Lp_mul_Lq_of_nonneg
          Real.HolderConjugate.two_two
          (ae_of_all _ fun z : ℝ => abs_nonneg z)
          (ae_of_all _ fun z : ℝ => abs_nonneg (fN z)) hidL2 hfNL2
        have hpow : ∀ a : ℝ, |a| ^ (2:ℝ) = a ^ 2 := fun a => by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        have h2 : ∫ z, |z| ^ (2:ℝ) ∂gaussianReal 0 1 = 1 := by
          rw [← integral_sq_gaussian]
          exact integral_congr_ae (ae_of_all _ fun z => hpow z)
        have h3 : ∫ z, |fN z| ^ (2:ℝ) ∂gaussianReal 0 1
            = ∫ z, fN z ^ 2 ∂gaussianReal 0 1 :=
          integral_congr_ae (ae_of_all _ fun z => hpow (fN z))
        rw [h2, h3, Real.one_rpow, one_mul] at hHold
        have h1 : ∫ z, z * fN z ∂gaussianReal 0 1
            ≤ ∫ z, |z| * |fN z| ∂gaussianReal 0 1 := by
          refine le_trans (le_abs_self _) ?_
          refine le_trans abs_integral_le_integral_abs ?_
          exact le_of_eq (integral_congr_ae
            (ae_of_all _ fun z => abs_mul z (fN z)))
        exact le_trans h1 hHold
      refine le_trans (ENNReal.ofReal_le_ofReal hCS2) ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg
        (integral_nonneg fun z => sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [ofReal_integral_eq_lintegral_ofReal hfN2int
        (ae_of_all _ fun z => sq_nonneg _), hA]
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      calc fN z ^ 2 ≤ |f z| ^ 2 :=
            sq_le_sq' (abs_le.1 (hfNabs z)).1 (abs_le.1 (hfNabs z)).2
        _ = f z ^ 2 := sq_abs _
    -- Q ≤ B^{1/2} : Cauchy–Schwarz 3
    have hQ2 : ∫⁻ x, ENNReal.ofReal ((f' x)⁻¹) ∂gaussianReal 0 1
        ≤ B ^ ((1:ℝ)/2) := by
      set ψ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((f' x)⁻¹) with hψdef
      set χ : ℝ → ℝ≥0∞ := fun _ => (1:ℝ≥0∞) with hχdef
      have hψm : AEMeasurable ψ (gaussianReal 0 1) :=
        (hf'meas.inv.ennreal_ofReal).aemeasurable
      have hχm : AEMeasurable χ (gaussianReal 0 1) := aemeasurable_const
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (gaussianReal 0 1)
        Real.HolderConjugate.two_two hψm hχm
      have hL : ∫⁻ a, (ψ * χ) a ∂gaussianReal 0 1
          = ∫⁻ x, ψ x ∂gaussianReal 0 1 :=
        lintegral_congr fun a => mul_one (ψ a)
      have hR2 : (∫⁻ a, χ a ^ (2:ℝ) ∂gaussianReal 0 1) ^ ((1:ℝ)/2) = 1 := by
        have h1 : ∫⁻ a, χ a ^ (2:ℝ) ∂gaussianReal 0 1 = 1 := by
          have h2 : ∀ a : ℝ, χ a ^ (2:ℝ) = 1 := fun _ => ENNReal.one_rpow _
          rw [lintegral_congr h2, lintegral_one, measure_univ]
        rw [h1, ENNReal.one_rpow]
      have hR1 : ∫⁻ a, ψ a ^ (2:ℝ) ∂gaussianReal 0 1 = B := by
        rw [hB]
        refine lintegral_congr_ae ?_
        filter_upwards [hposγ] with x hx
        have hh : ENNReal.ofReal ((f' x)⁻¹) ^ (2:ℝ)
            = ENNReal.ofReal ((f' x)⁻¹ ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt (inv_pos.2 hx))
            (by norm_num : (0:ℝ) ≤ 2),
            show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        exact hh
      calc ∫⁻ x, ψ x ∂gaussianReal 0 1
          = ∫⁻ a, (ψ * χ) a ∂gaussianReal 0 1 := hL.symm
        _ ≤ (∫⁻ a, ψ a ^ (2:ℝ) ∂gaussianReal 0 1) ^ ((1:ℝ)/2)
            * (∫⁻ a, χ a ^ (2:ℝ) ∂gaussianReal 0 1) ^ ((1:ℝ)/2) := hH
        _ = B ^ ((1:ℝ)/2) := by rw [hR1, hR2, mul_one]
    -- assemble the per-N chain
    calc gaussianReal 0 1 SN
        = ∫⁻ x, (φ₁ * φ₂) x ∂gaussianReal 0 1 := hLHS.symm
      _ ≤ (∫⁻ x, φ₁ x ^ (2:ℝ) ∂gaussianReal 0 1) ^ ((1:ℝ)/2)
          * (∫⁻ x, φ₂ x ^ (2:ℝ) ∂gaussianReal 0 1) ^ ((1:ℝ)/2) := hCS1
      _ = (∫⁻ x, SN.indicator (fun y => ENNReal.ofReal (f' y)) x
            ∂gaussianReal 0 1) ^ ((1:ℝ)/2)
          * (∫⁻ x, ENNReal.ofReal ((f' x)⁻¹) ∂gaussianReal 0 1)
            ^ ((1:ℝ)/2) := by rw [hsq₁, hsq₂]
      _ ≤ (A ^ ((1:ℝ)/2)) ^ ((1:ℝ)/2) * (B ^ ((1:ℝ)/2)) ^ ((1:ℝ)/2) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hP2 (by norm_num))
            (ENNReal.rpow_le_rpow hQ2 (by norm_num))
      _ = A ^ ((1:ℝ)/4) * B ^ ((1:ℝ)/4) := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            show ((1:ℝ)/2) * ((1:ℝ)/2) = (1:ℝ)/4 by norm_num]
      _ = (A * B) ^ ((1:ℝ)/4) :=
          (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
  -- let N → ∞
  have hlim : Tendsto (fun N : ℕ => gaussianReal 0 1 {x : ℝ | |f x| < (N:ℝ)})
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    have h := tendsto_measure_iUnion_atTop (μ := gaussianReal 0 1) hSmono
    rw [hSunion, measure_univ] at h
    exact h
  have hone : (1:ℝ≥0∞) ≤ (A * B) ^ ((1:ℝ)/4) :=
    le_of_tendsto hlim (Eventually.of_forall hkey)
  calc (1:ℝ≥0∞) = 1 ^ (4:ℝ) := (ENNReal.one_rpow _).symm
    _ ≤ ((A * B) ^ ((1:ℝ)/4)) ^ (4:ℝ) :=
        ENNReal.rpow_le_rpow hone (by norm_num)
    _ = (A * B) ^ (((1:ℝ)/4) * 4) := (ENNReal.rpow_mul _ _ _).symm
    _ = (A * B) ^ (1:ℝ) := by norm_num
    _ = A * B := ENNReal.rpow_one _

/-- **I3, `ℝ≥0∞` form** (v3 Lemma 2.5 — no v4 counterpart —
hypothesis-free core): for monotone
`f` with a.e. derivative `f' > 0` and `Z ~ N(0,1)`,
`1 ≤ E[f(Z)²] · E[1/f'(Z)²]` in `ℝ≥0∞` — no integrability assumptions. -/
theorem one_le_lintegral_sq_mul_lintegral_inv_sq {f f' : ℝ → ℝ}
    (hf : Monotone f) (hf' : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x)
    (hpos : ∀ᵐ x ∂volume, 0 < f' x) :
    1 ≤ (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂gaussianReal 0 1)
        * ∫⁻ x, ENNReal.ofReal ((f' x)⁻¹ ^ 2) ∂gaussianReal 0 1 := by
  -- replace `f'` by the canonical measurable representative
  set f'' : ℝ → ℝ :=
    fun x => (hf.stieltjesFunction.measure.rnDeriv volume x).toReal with hf''def
  have hf''meas : Measurable f'' := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hff'' : f' =ᵐ[volume] f'' := by
    filter_upwards [hf', hf.ae_hasDerivAt] with x hx hx'
    exact hx.unique hx'
  have hf'2 : ∀ᵐ x ∂volume, HasDerivAt f (f'' x) x := by
    filter_upwards [hf', hff''] with x hx hx2
    rwa [hx2] at hx
  have hpos2 : ∀ᵐ x ∂volume, 0 < f'' x := by
    filter_upwards [hpos, hff''] with x hx hx2
    rwa [hx2] at hx
  have hcore := stein_core hf hf''meas hf'2 hpos2
  have hγac : gaussianReal 0 1 ≪ (volume : Measure ℝ) :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hBeq : ∫⁻ x, ENNReal.ofReal ((f'' x)⁻¹ ^ 2) ∂gaussianReal 0 1
      = ∫⁻ x, ENNReal.ofReal ((f' x)⁻¹ ^ 2) ∂gaussianReal 0 1 := by
    refine lintegral_congr_ae ?_
    filter_upwards [hff''.filter_mono hγac.ae_le] with x hx
    rw [hx]
  rwa [hBeq] at hcore

/-- **I3, Bochner form** (v3 Lemma 2.5, squared outer form of v3 eq. (7);
no v4 counterpart): under `L²` hypotheses,
`1 ≤ E[f(Z)²] · E[1/f'(Z)²]`. -/
theorem one_le_integral_sq_mul_integral_inv_sq {f f' : ℝ → ℝ}
    (hf : Monotone f) (hf' : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x)
    (hpos : ∀ᵐ x ∂volume, 0 < f' x)
    (hf2 : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hg2 : Integrable (fun x => (f' x)⁻¹ ^ 2) (gaussianReal 0 1)) :
    1 ≤ (∫ x, f x ^ 2 ∂gaussianReal 0 1)
        * ∫ x, (f' x)⁻¹ ^ 2 ∂gaussianReal 0 1 := by
  have hcore := one_le_lintegral_sq_mul_lintegral_inv_sq hf hf' hpos
  rw [← ofReal_integral_eq_lintegral_ofReal hf2
      (ae_of_all _ fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hg2
      (ae_of_all _ fun x => sq_nonneg _),
    ← ENNReal.ofReal_mul (integral_nonneg fun x => sq_nonneg _)] at hcore
  exact ENNReal.one_le_ofReal.1 hcore

/-- **I3, outer form** (v3 Lemma 2.5, v3 eq. (7) verbatim; no v4
counterpart — this is the statement `SignedRoot.lean` uses for `1 ≤ 2Γ`
under Lane-C decision D7, in place of v4's Cacoullos Lemma 2.7):
`1 ≤ √(E[f(Z)²] · E[1/f'(Z)²])`. -/
theorem one_le_sqrt_integral_sq_mul_integral_inv_sq {f f' : ℝ → ℝ}
    (hf : Monotone f) (hf' : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x)
    (hpos : ∀ᵐ x ∂volume, 0 < f' x)
    (hf2 : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hg2 : Integrable (fun x => (f' x)⁻¹ ^ 2) (gaussianReal 0 1)) :
    1 ≤ Real.sqrt ((∫ x, f x ^ 2 ∂gaussianReal 0 1)
        * ∫ x, (f' x)⁻¹ ^ 2 ∂gaussianReal 0 1) := by
  have h := one_le_integral_sq_mul_integral_inv_sq hf hf' hpos hf2 hg2
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt h

end KyleUniqueness
