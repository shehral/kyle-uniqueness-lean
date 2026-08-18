/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Gaussian helper lemmas

Mathlib-only support layer for the Kyle-uniqueness formalization
(arXiv:2607.23585v2): the items recorded as MISSING in
`blueprint/mathlib_api_audit.md` §10 (items 1–4), plus the small Gaussian
integral toolkit consumed by the pricing-rule bridge (`CondExpBridge.lean`).

## Audit §10 status at pin `81a5d257` (tag v4.32.0)

1. *`NoAtoms (gaussianReal μ v)`*: the atoms API was renamed at this pin —
   `MeasureTheory.NullSingletonClass` replaces `NoAtoms` (deprecated alias
   dated 2026-06-09), and `ProbabilityTheory.nullSingletonClass_gaussianReal`
   ALREADY exists for `v ≠ 0`; the audit's grep for `NoAtoms` missed it. We
   register the instance for the standard normal (`v = 1`) so typeclass
   search finds it, and record the audit correction here. Bonus discovery:
   `exists_accPt_of_nullSingletonClass` (positive measure ⇒ accumulation
   point) also already exists at the pin — it is the exact glue hard-block 5
   (blueprint node L2) was budgeted to build.
2. *`HasDerivAt ϱ`*: proved below (`hasDerivAt_gaussianPDFReal`, general
   mean/variance; the standard-normal `ϱ′(x) = −x·ϱ(x)` is the special case
   `hasDerivAt_gaussianPDFReal_std`).
3. *Gaussian tail FTC* `∫_{Ioi a} x·ϱ(x) dx = ϱ(a)`: proved below
   (`integral_Ioi_id_mul_gaussianPDFReal_std`).
4. *Atomless transfer glue*: proved below (`NullSingletonClass` under
   `withDensity` and under injective pushforward; the diagonal is null for a
   product with atomless second factor; positive measure ⇒ infinite set).

All declarations are stated against plain Mathlib; nothing here mentions the
Kyle model.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal Topology

namespace KyleUniqueness

/-! ## Evaluation and bounds -/

/-- Unfolding of the Gaussian pdf at an `NNReal.mk` variance, with the
coercion already eliminated (definitional; used to keep the anonymous
constructor's coercion out of algebraic goals). -/
lemma gaussianPDFReal_eval (m : ℝ) (w : ℝ) (hw : 0 ≤ w) (x : ℝ) :
    gaussianPDFReal m ⟨w, hw⟩ x
      = (√(2 * π * w))⁻¹ * rexp (-(x - m) ^ 2 / (2 * w)) := rfl

/-- The Gaussian pdf is bounded by its value at the mean:
`ϱ_{μ,v}(x) ≤ (√(2πv))⁻¹` (used for `Integrable`-by-domination arguments;
holds trivially at `v = 0` where both sides are `0`). -/
lemma gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  nth_rewrite 2 [← mul_one ((√(2 * π * v))⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_one_iff.mpr ?_
  rw [neg_div]
  exact neg_nonpos.mpr (by positivity)

/-! ## Audit §10 item 1: atomlessness of `gaussianReal`

Present at the pin as `nullSingletonClass_gaussianReal` (for `v ≠ 0`); we
only register the standard-normal instance. -/

instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal one_ne_zero

/-! ## Audit §10 item 2: derivative of the Gaussian pdf -/

/-- The Gaussian pdf is everywhere differentiable, with
`ϱ_{μ,v}′(x) = −((x − μ)/v)·ϱ_{μ,v}(x)` (`v ≠ 0`). -/
lemma hasDerivAt_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  have hv0 : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hsub : HasDerivAt (fun y : ℝ => y - μ) 1 x := (hasDerivAt_id x).sub_const μ
  -- chain rule through `z ↦ z²`, negation, division by `2v`, `exp`, and the
  -- constant prefactor
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

/-- Standard-normal case: `ϱ′(x) = −x·ϱ(x)` (audit §10 item 2 as stated). -/
lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  simpa using hasDerivAt_gaussianPDFReal 0 one_ne_zero x

/-- The Gaussian pdf is continuous. -/
@[fun_prop]
lemma continuous_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Continuous (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- The Gaussian pdf vanishes at `+∞`. -/
lemma tendsto_gaussianPDFReal_atTop (μ : ℝ) (v : ℝ≥0) :
    Tendsto (gaussianPDFReal μ v) atTop (𝓝 0) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [gaussianPDFReal_zero_var]
    exact tendsto_const_nhds
  have hv0 : (0 : ℝ) < (v : ℝ) := by positivity
  have h1 : Tendsto (fun y : ℝ => (y - μ) ^ 2 / (2 * (v : ℝ))) atTop atTop :=
    Tendsto.atTop_div_const (by positivity)
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-μ) tendsto_id))
  have h2 : Tendsto (fun y : ℝ => -(y - μ) ^ 2 / (2 * (v : ℝ))) atTop atBot := by
    simp only [neg_div]
    exact tendsto_neg_atBot_iff.mpr h1
  have h3 := Real.tendsto_exp_atBot.comp h2
  have h4 := h3.const_mul ((√(2 * π * (v : ℝ)))⁻¹)
  simpa [gaussianPDFReal_def, Function.comp_def, sub_eq_add_neg] using h4

/-! ## Integrability transfers between `gaussianReal` and weighted Lebesgue -/

/-- The identity is integrable w.r.t. any Gaussian measure (the Gaussian has
a first moment). Missing at the pin under this name; immediate from
`memLp_id_gaussianReal`. -/
lemma integrable_id_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    Integrable id (gaussianReal μ v) :=
  memLp_one_iff_integrable.mp
    (by simpa using memLp_id_gaussianReal (μ := μ) (v := v) 1)

/-- Transfer of integrability from `gaussianReal` to pdf-weighted Lebesgue:
`f` is `gaussianReal`-integrable iff `ϱ·f` is Lebesgue-integrable
(`v ≠ 0`). -/
lemma integrable_gaussianReal_iff {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal μ v) ↔
      Integrable (fun x => gaussianPDFReal μ v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

/-- `x·ϱ_{μ,v}(x)` is Lebesgue-integrable. -/
lemma integrable_id_mul_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x => x * gaussianPDFReal μ v x) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have := (integrable_gaussianReal_iff hv (f := id)).mp
      (integrable_id_gaussianReal μ v)
    simpa [mul_comm] using this

/-! ## Audit §10 item 3: Gaussian tail FTC -/

/-- `∫_{(a,∞)} x·ϱ(x) dx = ϱ(a)` for the standard normal density: the tail
first-moment identity (used by blueprint nodes A4, F1, I1). Proof: FTC-2 on
`(a, ∞)` applied to `−ϱ`, whose derivative is `x·ϱ(x)`
(`hasDerivAt_gaussianPDFReal_std`), with `ϱ → 0` at `+∞`. -/
lemma integral_Ioi_id_mul_gaussianPDFReal_std (a : ℝ) :
    ∫ x in Ioi a, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 a := by
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt (fun y => -gaussianPDFReal 0 1 y)
        (x * gaussianPDFReal 0 1 x) x := by
    intro x _
    have h := (hasDerivAt_gaussianPDFReal_std x).neg
    rwa [neg_mul, neg_neg] at h
  have hint : IntegrableOn (fun x => x * gaussianPDFReal 0 1 x) (Ioi a) :=
    (integrable_id_mul_gaussianPDFReal 0 1).integrableOn
  have htend : Tendsto (fun y => -gaussianPDFReal 0 1 y) atTop (𝓝 0) := by
    simpa using (tendsto_gaussianPDFReal_atTop 0 1).neg
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  simpa using this

/-! ## Audit §10 item 4: atomlessness transfer glue -/

/-- `withDensity` preserves atomlessness. -/
lemma NullSingletonClass.withDensity {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} [NullSingletonClass μ]
    (f : α → ℝ≥0∞) : NullSingletonClass (μ.withDensity f) := by
  refine ⟨fun a => ?_⟩
  rw [withDensity_apply _ (measurableSet_singleton a),
    Measure.restrict_eq_zero.mpr (measure_singleton a)]
  simp

/-- The pushforward of an atomless measure under an injective measurable map
is atomless. -/
lemma nullSingletonClass_map_of_injective {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] {μ : Measure α}
    [NullSingletonClass μ] {g : α → β} (hg : Measurable g)
    (hginj : Function.Injective g) : NullSingletonClass (μ.map g) := by
  refine ⟨fun b => ?_⟩
  rw [Measure.map_apply hg (measurableSet_singleton b)]
  exact Set.Subsingleton.measure_zero
    (fun x hx y hy => hginj (hx.trans hy.symm)) μ

/-- The diagonal of `ℝ × ℝ` is null for a product measure whose second
factor is atomless (blueprint node D1's glue: the posterior product charges
no diagonal). -/
lemma measure_prod_diagonal_eq_zero {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    [NullSingletonClass ν] : (μ.prod ν) (Set.diagonal ℝ) = 0 := by
  have hdiag : MeasurableSet (Set.diagonal ℝ) :=
    isClosed_diagonal.measurableSet
  rw [Measure.prod_apply hdiag]
  have h : ∀ x : ℝ, ν (Prod.mk x ⁻¹' Set.diagonal ℝ) = 0 := by
    intro x
    have hx : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
      ext y; simp [Set.diagonal, eq_comm]
    rw [hx]
    exact measure_singleton x
  simp [h]

/-- A set of positive measure under an atomless measure is infinite
(blueprint node L2's glue; contrapositive of `Set.Finite.measure_zero`). -/
lemma infinite_of_measure_ne_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [NullSingletonClass μ] {s : Set α} (hs : μ s ≠ 0) :
    s.Infinite :=
  fun hfin => hs (hfin.measure_zero μ)

/-! ## Translation of Gaussian integrals to weighted Lebesgue integrals

The change-of-variables `y = t + u` sending the noise law `N(0, v)` to
`N(t, v)`, in both Bochner and lintegral forms. These are the workhorses of
the order-flow disintegration in `CondExpBridge.lean`: the inner noise
integral `∫ f(t + u) N(0,v)(du)` becomes the Lebesgue integral of `f`
against the shifted kernel `y ↦ ϱ_v(y − t)`. -/

/-- Bochner form: `∫ f(t+u) dN(0,v)(u) = ∫ ϱ_v(y − t)·f(y) dy` (`v ≠ 0`). -/
lemma integral_comp_add_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) :
    ∫ u, f (t + u) ∂gaussianReal 0 v
      = ∫ y, gaussianPDFReal 0 v (y - t) * f y := by
  have hmap : (gaussianReal 0 v).map (t + ·) = gaussianReal t v := by
    simpa using gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) t
  have hfae : AEStronglyMeasurable f ((gaussianReal 0 v).map (t + ·)) := by
    rw [hmap]
    exact hf.mono_ac (gaussianReal_absolutelyContinuous _ hv)
  calc ∫ u, f (t + u) ∂gaussianReal 0 v
      = ∫ y, f y ∂((gaussianReal 0 v).map (t + ·)) :=
        (integral_map (measurable_const_add t).aemeasurable hfae).symm
    _ = ∫ y, f y ∂gaussianReal t v := by rw [hmap]
    _ = ∫ y, gaussianPDFReal t v y • f y :=
        integral_gaussianReal_eq_integral_smul hv
    _ = ∫ y, gaussianPDFReal 0 v (y - t) * f y := by
        congr 1 with y
        rw [gaussianPDFReal_sub, zero_add, smul_eq_mul]

/-- lintegral form: `∫⁻ f(t+u) dN(0,v)(u) = ∫⁻ ϱ_v(y − t)·f(y) dy`
(`v ≠ 0`). -/
lemma lintegral_comp_add_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f (t + u) ∂gaussianReal 0 v
      = ∫⁻ y, gaussianPDF 0 v (y - t) * f y := by
  have hmap : (gaussianReal 0 v).map (t + ·) = gaussianReal t v := by
    simpa using gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) t
  calc ∫⁻ u, f (t + u) ∂gaussianReal 0 v
      = ∫⁻ y, f y ∂((gaussianReal 0 v).map (t + ·)) :=
        (lintegral_map hf (measurable_const_add t)).symm
    _ = ∫⁻ y, f y ∂gaussianReal t v := by rw [hmap]
    _ = ∫⁻ y, (gaussianPDF t v * f) y := by
        rw [gaussianReal_of_var_ne_zero _ hv,
          lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF t v) hf]
    _ = ∫⁻ y, gaussianPDF 0 v (y - t) * f y := by
        congr 1 with y
        rw [Pi.mul_apply, gaussianPDF, gaussianPDF, gaussianPDFReal_sub, zero_add]

/-- lintegral form, `ENNReal.ofReal` spelling (same statement as
`lintegral_comp_add_gaussianReal`, definitionally). -/
lemma lintegral_comp_add_gaussianReal' {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f (t + u) ∂gaussianReal 0 v
      = ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 v (y - t)) * f y :=
  lintegral_comp_add_gaussianReal hv t hf

/-- The shifted Gaussian kernel has total lintegral one:
`∫⁻ ϱ_v(y − t) dy = 1` (`v ≠ 0`). -/
lemma lintegral_gaussianPDF_sub {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ∫⁻ y, gaussianPDF 0 v (y - t) = 1 := by
  calc ∫⁻ y, gaussianPDF 0 v (y - t)
      = ∫⁻ y, gaussianPDF t v y := by
        congr 1 with y
        rw [gaussianPDF, gaussianPDF, gaussianPDFReal_sub, zero_add]
    _ = 1 := lintegral_gaussianPDF_eq_one t hv

/-- `ENNReal.ofReal` spelling of `lintegral_gaussianPDF_sub`
(definitionally the same). -/
lemma lintegral_ofReal_gaussianPDFReal_sub {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 v (y - t)) = 1 :=
  lintegral_gaussianPDF_sub hv t

/-- The shifted Gaussian kernel has total integral one:
`∫ ϱ_v(y − t) dy = 1` (`v ≠ 0`). -/
lemma integral_gaussianPDFReal_sub' {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ∫ y, gaussianPDFReal 0 v (y - t) = 1 := by
  calc ∫ y, gaussianPDFReal 0 v (y - t)
      = ∫ y, gaussianPDFReal t v y := by
        congr 1 with y
        rw [gaussianPDFReal_sub, zero_add]
    _ = 1 := integral_gaussianPDFReal_eq_one t hv

/-! ## Low moments of the Gaussian -/

/-- Second moment of the standard normal: `∫ x·x dN(0,1) = 1` (from
`variance_id_gaussianReal` and the zero mean). -/
lemma integral_mul_self_gaussianReal_std :
    ∫ x, x * x ∂(gaussianReal 0 1 : Measure ℝ) = 1 := by
  have hmem : MemLp id 2 (gaussianReal (0 : ℝ) 1) := by
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  have hv := variance_eq_sub hmem
  rw [variance_id_gaussianReal] at hv
  simp only [Pi.pow_apply, id_eq] at hv
  rw [integral_id_gaussianReal] at hv
  norm_num at hv
  have h2 : (fun x : ℝ => x * x) = fun x : ℝ => x ^ 2 :=
    funext fun x => (pow_two x).symm
  rw [h2]
  linarith

/-- pdf-level mean: `∫ x·ϱ_{m,v}(x) dx = m` (`v ≠ 0`). -/
lemma integral_id_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, x * gaussianPDFReal m v x = m := by
  have h : ∫ x, x ∂gaussianReal m v = m := integral_id_gaussianReal
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  calc ∫ x, x * gaussianPDFReal m v x
      = ∫ x, gaussianPDFReal m v x • x := by
        congr 1 with x
        rw [smul_eq_mul, mul_comm]
    _ = m := h

/-! ## The Kyle complete-the-square identity

The bivariate Gaussian factorization behind eq. (3) of the paper: for the
affine strategy with slope `c = σ/τ`, the product of the noise kernel and
the prior density factorizes as (density of `N(0, 2σ²)` in `y`) × (density
of the posterior `N(λy, τ²/2)` in the centred value `a`), where
`λ = τ/(2σ)` is Kyle's price impact. This one identity is the entire
computational content of the existence half of Theorem 1.1. -/

/-- Complete-the-square: for `σ, τ > 0`, all `y a : ℝ`,
`ϱ_{0,σ²}(y − (σ/τ)a) · ϱ_{0,τ²}(a) = ϱ_{0,2σ²}(y) · ϱ_{τy/(2σ), τ²/2}(a)`. -/
lemma gaussianPDFReal_mul_gaussianPDFReal_kyle {σ τ : ℝ} (hσ : 0 < σ)
    (hτ : 0 < τ) (y a : ℝ) :
    gaussianPDFReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ (y - σ / τ * a) *
        gaussianPDFReal 0 ⟨τ ^ 2, sq_nonneg τ⟩ a =
      gaussianPDFReal 0 ⟨2 * σ ^ 2, by positivity⟩ y *
        gaussianPDFReal (τ / (2 * σ) * y) ⟨τ ^ 2 / 2, by positivity⟩ a := by
  have hσ' : σ ≠ 0 := hσ.ne'
  have hτ' : τ ≠ 0 := hτ.ne'
  rw [gaussianPDFReal_eval, gaussianPDFReal_eval, gaussianPDFReal_eval,
    gaussianPDFReal_eval]
  simp only [sub_zero]
  rw [mul_mul_mul_comm, mul_mul_mul_comm ((√(2 * π * (2 * σ ^ 2)))⁻¹)]
  congr 1
  · -- prefactors: `(2πσ²)(2πτ²) = (2π·2σ²)(2π·τ²/2)`
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    congr 2
    ring
  · -- exponents: complete the square in `a`
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring

/-- The standard normal density is nonincreasing in the distance from the
mean: `|s| ≤ |t| ⟹ ϱ(t) ≤ ϱ(s)` (blueprint node R1's interval bound). -/
lemma gaussianPDFReal_std_anti {s t : ℝ} (h : |s| ≤ |t|) :
    gaussianPDFReal 0 1 t ≤ gaussianPDFReal 0 1 s := by
  simp only [gaussianPDFReal_def]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_exp]
  have h2 : s ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs s, ← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg s) h 2
  simp only [sub_zero, mul_one]
  linarith

/-- The standard normal density is even. -/
lemma gaussianPDFReal_std_neg (t : ℝ) :
    gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
  simp only [gaussianPDFReal_def]
  push_cast
  exact congrArg (fun z => (Real.sqrt (2 * Real.pi * 1))⁻¹ * Real.exp z)
    (by ring)

/-- A Gaussian-a.e. property holds Lebesgue-a.e. (the Gaussian density is
everywhere positive, so Gaussian null sets are Lebesgue null sets). -/
lemma ae_volume_of_ae_gaussianReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {p : ℝ → Prop} (h : ∀ᵐ x ∂gaussianReal μ v, p x) :
    ∀ᵐ x ∂(volume : Measure ℝ), p x := by
  rw [gaussianReal_of_var_ne_zero _ hv] at h
  have h2 := (ae_withDensity_iff'
    (measurable_gaussianPDF μ v).aemeasurable).mp h
  filter_upwards [h2] with x hx
  refine hx ?_
  rw [gaussianPDF]
  exact (ENNReal.ofReal_pos.mpr (gaussianPDFReal_pos μ v x hv)).ne'

/-- Gaussian complete-the-square for the `K_x` kernel (v3 App. A, proof of
Lemma 2.3): `ϱ(y−x)·ϱ(y−a) = e^{(x−d)(a−d)} · ϱ(y−(x+a−d)) · ϱ(y−d)`. -/
lemma gaussianPDFReal_std_mul_eq_exp_mul (x a d y : ℝ) :
    gaussianPDFReal 0 1 (y - x) * gaussianPDFReal 0 1 (y - a)
      = Real.exp ((x - d) * (a - d))
        * (gaussianPDFReal 0 1 (y - (x + a - d)) * gaussianPDFReal 0 1 (y - d)) := by
  have hL : gaussianPDFReal 0 1 (y - x) * gaussianPDFReal 0 1 (y - a)
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-(y - x) ^ 2 / 2 + -(y - a) ^ 2 / 2) := by
    simp only [gaussianPDFReal_def]
    push_cast
    simp only [sub_zero, mul_one]
    rw [Real.exp_add]
    ring
  have hR : Real.exp ((x - d) * (a - d))
        * (gaussianPDFReal 0 1 (y - (x + a - d)) * gaussianPDFReal 0 1 (y - d))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp ((x - d) * (a - d) + (-(y - (x + a - d)) ^ 2 / 2
            + -(y - d) ^ 2 / 2)) := by
    simp only [gaussianPDFReal_def]
    push_cast
    simp only [sub_zero, mul_one]
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hL, hR]
  exact congrArg (fun t => (Real.sqrt (2 * Real.pi))⁻¹
    * (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp t) (by ring)

/-- The `K_x` kernel against a shifted Gaussian denominator integrates to
the completed square: `∫ ϱ(y−x)ϱ(y−a)/ϱ(y−d) dy = e^{(x−d)(a−d)}` (v3
App. A, proof of Lemma 2.3). -/
lemma lintegral_gaussianPDFReal_std_mul_div (x a d : ℝ) :
    ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 1 (y - x)
        * gaussianPDFReal 0 1 (y - a) / gaussianPDFReal 0 1 (y - d))
      = ENNReal.ofReal (Real.exp ((x - d) * (a - d))) := by
  have hpt : ∀ y : ℝ, gaussianPDFReal 0 1 (y - x) * gaussianPDFReal 0 1 (y - a)
      / gaussianPDFReal 0 1 (y - d)
      = Real.exp ((x - d) * (a - d)) * gaussianPDFReal 0 1 (y - (x + a - d)) := by
    intro y
    rw [gaussianPDFReal_std_mul_eq_exp_mul x a d y,
      show Real.exp ((x - d) * (a - d)) * (gaussianPDFReal 0 1 (y - (x + a - d))
          * gaussianPDFReal 0 1 (y - d))
        = gaussianPDFReal 0 1 (y - d) * (Real.exp ((x - d) * (a - d))
          * gaussianPDFReal 0 1 (y - (x + a - d))) from by ring,
      mul_div_cancel_left₀ _ (gaussianPDFReal_pos 0 1 (y - d) one_ne_zero).ne']
  calc ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 1 (y - x)
        * gaussianPDFReal 0 1 (y - a) / gaussianPDFReal 0 1 (y - d))
      = ∫⁻ y, ENNReal.ofReal (Real.exp ((x - d) * (a - d)))
          * ENNReal.ofReal (gaussianPDFReal 0 1 (y - (x + a - d))) := by
        refine lintegral_congr fun y => ?_
        rw [hpt y, ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ENNReal.ofReal (Real.exp ((x - d) * (a - d)))
          * ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 1 (y - (x + a - d))) := by
        have hm : Measurable fun y : ℝ =>
            ENNReal.ofReal (gaussianPDFReal 0 1 (y - (x + a - d))) :=
          ((measurable_gaussianPDFReal 0 1).comp
            (measurable_id.sub_const _)).ennreal_ofReal
        exact lintegral_const_mul _ hm
    _ = ENNReal.ofReal (Real.exp ((x - d) * (a - d))) := by
        rw [lintegral_ofReal_gaussianPDFReal_sub one_ne_zero, mul_one]

/-- Standard-normal complete-the-square with literal `ℝ≥0` variances (the
`σ = τ = 1` instance of the Kyle factorization, stated free of `NNReal.mk`
anonymous constructors so that all downstream rewrites stay
instances-transparent): `ϱ(y − v)·ϱ(v) = ϱ_{0,2}(y)·ϱ_{y/2,1/2}(v)`.
The computational core of the affine-strategy regression (blueprint node
N1). -/
lemma gaussianPDFReal_mul_gaussianPDFReal_std (y v : ℝ) :
    gaussianPDFReal 0 1 (y - v) * gaussianPDFReal 0 1 v
      = gaussianPDFReal 0 2 y * gaussianPDFReal (y / 2) (1 / 2) v := by
  simp only [gaussianPDFReal_def]
  push_cast
  rw [mul_mul_mul_comm, mul_mul_mul_comm ((Real.sqrt (2 * Real.pi * 2))⁻¹)]
  congr 1
  · -- prefactors: `(2π·1)(2π·1) = (2π·2)(2π·(1/2))`
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    congr 2
    ring
  · -- exponents: complete the square in `v`
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring

end KyleUniqueness
