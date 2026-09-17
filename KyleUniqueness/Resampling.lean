/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Regularity

/-!
# Conditional resampling (blueprint node E1; v4 Lemma 2.6 = v3 Lemma 2.4)

Formalization of Lemma 2.6 of Monteiro & Tourky, *The one-period Gaussian
Kyle model has exactly one equilibrium* (arXiv:2607.23585, **v4** of
2026-08-20; the identical statement is v3 Lemma 2.4). Numbering below is
v4's.

## Route (Lane-C decision D4)

The paper obtains the conditionally independent replica `V⁽¹⁾` abstractly,
from Kallenberg's transfer theorem on an extension of the probability
space. Mathlib has no transfer theorem and no posterior-disintegration API
for `condDistrib` at the pin (`81a5d257`), so we **construct the law of the
triple explicitly**: `resamplingMeasure φ` is the single flat Lebesgue
`withDensity` on `ℝ³` (coordinates `(v₀, v₁, y)`) with density

`ϱ(v₀)·ϱ(y − φ(v₀)) · ϱ(v₁)·ϱ(y − φ(v₁)) / p(y)`,

`p` the flow density of `Definitions.lean`. Every clause of Lemma 2.6 is
then a Tonelli/Fubini computation against that density — no `condExp` and
no kernel algebra appear on `μ₃`, and clauses (iii), (iv) are stated in
**test-function form** (against bounded Borel test functions), which is the
form v4 §5 actually consumes. Two master Tonelli identities
(`lintegral_resampling_v0/v1`, private) reduce every statement to the two
one-dimensional kernel integrals
`∫ ϱ(v)ϱ(y − φ v) dv = p(y)` and `∫ ϱ(v)ϱ(y − φ v) dy = ϱ(v)`.

## Main statements

* `resamplingMeasure`, `isProbabilityMeasure_resamplingMeasure` — the law
  of `(V⁰, V¹, Y)` and its total mass.
* `resamplingMeasure_map_swap` — **(i)**: `(V⁰, V¹, Y)` and `(V¹, V⁰, Y)`
  have the same law (exchangeability).
* `resamplingMeasure_map_snd` / `resamplingMeasure_map_fst` — **(ii)**: the
  `(V¹, Y)` and `(V⁰, Y)` marginals both have density `ϱ(v)·ϱ(y − φ(v))`,
  i.e. both pairs are distributed as `(V, Y)`.
* `resamplingMeasure_map_v1` / `resamplingMeasure_map_v0` /
  `resamplingMeasure_map_y` — the one-dimensional marginals: both replicas
  are standard normal, and `Y` has law `p(y) dy`.
* `integral_v1_mul_eq_inverseRegression` — **(iii)** in test-function form:
  `E[V¹·g(V⁰, Y)] = E[P(Y)·g(V⁰, Y)]` for bounded Borel `g`, i.e.
  `E[V¹ ∣ Y, V⁰] = P(Y)`.
* `integral_v1_mul_eq_gaussianSmoothing` — **(iv)** in test-function form:
  `E[V¹·g(V⁰)] = E[F(φ(V))·g(V)]` for bounded Borel `g`, i.e.
  `E[V¹ ∣ V⁰] = F(φ(V⁰))`.
* `integral_v1_mul_comp_eq_gaussianSmoothing`,
  `integral_v0_mul_v1_resampling` — the moment identities v4 Proposition
  5.1 consumes: `E[V¹·k(φ(V⁰))] = E[F(φ(V))·k(φ(V))]` for bounded Borel `k`
  (this is the `n → ∞` input of (5.2) with `k` the lattice truncation), and
  `E[V⁰·V¹] = E[P(Y)²]`.
* `integrable_v1_resampling`, `integrable_v0_resampling`,
  `integrable_inverseRegression_resampling`,
  `integrable_v0_mul_v1_resampling` — the accompanying integrability
  (first and second moments under `μ₃`).
* `integrable_gaussianSmoothing_comp`,
  `gaussianSmoothing_comp_ae_eq_condExp_condExp` — node R2b, the clause of
  v4 Lemma 2.3 deferred by `Regularity.lean`: `F(φ(V)) ∈ L¹` and
  `F(φ(V)) = E[E[V ∣ Y] ∣ V]` almost surely on `stdModel`.

## Hypotheses beyond the paper

None, other than the explicit `Measurable φ` that the paper carries as
"Borel `φ`" throughout §2, and the boundedness hypothesis on the test
functions of (iii), (iv) — which replaces the paper's `L¹`/`condExp`
formulation and is what makes the identities unconditional in `φ` (the
paper's `φ` need not be integrable, and `Π(V)` need not be either).
`resamplingMeasure φ` is a *definition*, not an assumed extension of the
probability space: clause (ii) is the proof that it realises the paper's
`V⁽¹⁾`.
-/

open MeasureTheory ProbabilityTheory Real Filter Set

open scoped ENNReal NNReal Topology

namespace KyleUniqueness

/-- The joint Lebesgue density of `(V, Y)`: `ϱ(v)·ϱ(y − φ(v))`. -/
private noncomputable def jd (φ : ℝ → ℝ) (v y : ℝ) : ℝ :=
  stdNormalPDF v * stdNormalPDF (y - φ v)

private lemma jd_apply (φ : ℝ → ℝ) (v y : ℝ) :
    stdNormalPDF v * stdNormalPDF (y - φ v) = jd φ v y := rfl

private lemma jd_nonneg (φ : ℝ → ℝ) (v y : ℝ) : 0 ≤ jd φ v y :=
  mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

private lemma measurable_jd {φ : ℝ → ℝ} (hφ : Measurable φ) {α : Type*}
    [MeasurableSpace α] {a b : α → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => jd φ (a x) (b x) := by
  refine Measurable.mul ?_ ?_
  · exact (measurable_gaussianPDFReal 0 1).comp ha
  · exact (measurable_gaussianPDFReal 0 1).comp (hb.sub (hφ.comp ha))

private lemma measurable_jd_left {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Measurable fun v => jd φ v y := by
  exact measurable_jd hφ measurable_id measurable_const

private lemma measurable_jd_right {φ : ℝ → ℝ} (hφ : Measurable φ) (v : ℝ) :
    Measurable fun y => jd φ v y := by
  exact measurable_jd hφ measurable_const measurable_id

private lemma integrable_jd_left {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => jd φ v y) := by
  have hb : Integrable (fun v => stdNormalPDF v
      * (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹) (volume : Measure ℝ) :=
    (integrable_gaussianPDFReal 0 1).mul_const _
  refine Integrable.mono' hb
    (measurable_jd hφ measurable_id measurable_const).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (jd_nonneg _ _ _), jd]
  exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le _ _ _)
    (gaussianPDFReal_nonneg _ _ _)

private lemma integral_jd_left (φ : ℝ → ℝ) (y : ℝ) :
    ∫ v, jd φ v y = flowDensity φ y := by
  rw [flowDensity, integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero]
  simp [jd, stdNormalPDF, smul_eq_mul]

private lemma integrable_jd_right (φ : ℝ → ℝ) (v : ℝ) :
    Integrable (fun y => jd φ v y) := by
  simp only [jd]
  refine Integrable.const_mul ?_ _
  have : (fun y => stdNormalPDF (y - φ v)) = gaussianPDFReal (φ v) 1 := by
    funext y
    rw [stdNormalPDF, gaussianPDFReal_sub, zero_add]
  rw [this]
  exact integrable_gaussianPDFReal _ _

private lemma integral_jd_right (φ : ℝ → ℝ) (v : ℝ) :
    ∫ y, jd φ v y = stdNormalPDF v := by
  simp only [jd]
  rw [integral_const_mul, stdNormalPDF, integral_gaussianPDFReal_sub' one_ne_zero, mul_one]

private lemma lintegral_jd_left (φ : ℝ → ℝ) (y : ℝ)
    (hφ : Measurable φ) :
    ∫⁻ v, ENNReal.ofReal (jd φ v y) = ENNReal.ofReal (flowDensity φ y) := by
  rw [← integral_jd_left φ y,
    ofReal_integral_eq_lintegral_ofReal (integrable_jd_left hφ y)
      (ae_of_all _ fun v => jd_nonneg _ _ _)]

private lemma lintegral_jd_right (φ : ℝ → ℝ) (v : ℝ) :
    ∫⁻ y, ENNReal.ofReal (jd φ v y) = ENNReal.ofReal (stdNormalPDF v) := by
  rw [← integral_jd_right φ v,
    ofReal_integral_eq_lintegral_ofReal (integrable_jd_right φ v)
      (ae_of_all _ fun y => jd_nonneg _ _ _)]

/-- The flow density is continuous (dominated convergence with the uniform
bound `ϱ ≤ ϱ(0)`); only its measurability is used below. -/
private lemma continuous_flowDensity {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Continuous (flowDensity φ) := by
  have hrwp : flowDensity φ = fun y =>
      ∫ v, gaussianPDFReal 0 1 (y - φ v) ∂gaussianReal 0 1 := rfl
  rw [hrwp]
  refine continuous_of_dominated
    (bound := fun _ => (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹)
    (fun y => ((measurable_gaussianPDFReal 0 1).comp
      (measurable_const.sub hφ)).aestronglyMeasurable)
    (fun y => ae_of_all _ fun v => ?_) (integrable_const _)
    (ae_of_all _ fun v => ?_)
  · rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le _ _ _
  · exact (continuous_gaussianPDFReal 0 1).comp
      (continuous_id.sub continuous_const)

/-! ## The resampling measure -/

/-- The density of the resampling measure in factored form. -/
private noncomputable def rd (φ : ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  jd φ q.1 q.2.2 * jd φ q.2.1 q.2.2 / flowDensity φ q.2.2

private lemma rd_nonneg {φ : ℝ → ℝ} (hφ : Measurable φ) (q : ℝ × ℝ × ℝ) :
    0 ≤ rd φ q :=
  div_nonneg (mul_nonneg (jd_nonneg _ _ _) (jd_nonneg _ _ _))
    (lemma21_flowDensity_pos hφ _).le

private lemma measurable_rd {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (rd φ) :=
  ((measurable_jd hφ measurable_fst measurable_snd.snd).mul
      (measurable_jd hφ measurable_snd.fst measurable_snd.snd)).div
    ((continuous_flowDensity hφ).measurable.comp measurable_snd.snd)

/-- **The conditional-resampling measure** (v4 Lemma 2.6): the law of the
exchangeable triple `(V⁰, V¹, Y)` on `ℝ³`, given as one flat Lebesgue
`withDensity` with density
`ϱ(v₀)·ϱ(y − φ(v₀))·ϱ(v₁)·ϱ(y − φ(v₁)) / p(y)`. -/
noncomputable def resamplingMeasure (φ : ℝ → ℝ) : Measure (ℝ × ℝ × ℝ) :=
  volume.withDensity fun q => ENNReal.ofReal
    (stdNormalPDF q.1 * stdNormalPDF (q.2.2 - φ q.1) * stdNormalPDF q.2.1
      * stdNormalPDF (q.2.2 - φ q.2.1) / flowDensity φ q.2.2)

private lemma resamplingMeasure_eq (φ : ℝ → ℝ) :
    resamplingMeasure φ = volume.withDensity fun q => ENNReal.ofReal (rd φ q) := by
  have h : (fun q : ℝ × ℝ × ℝ => ENNReal.ofReal
      (stdNormalPDF q.1 * stdNormalPDF (q.2.2 - φ q.1) * stdNormalPDF q.2.1
        * stdNormalPDF (q.2.2 - φ q.2.1) / flowDensity φ q.2.2))
      = fun q => ENNReal.ofReal (rd φ q) := by
    funext q
    refine congrArg _ ?_
    simp only [rd, jd]
    ring
  rw [resamplingMeasure, h]

/-! ## Tonelli for the flat triple density -/

/-- Tonelli on `ℝ³ = ℝ × (ℝ × ℝ)` in the order `y` (outer), `v₁`, `v₀`
(inner). -/
private lemma lintegral_triple_v0 {f : ℝ × ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q : ℝ × ℝ × ℝ, f q = ∫⁻ y, ∫⁻ v₁, ∫⁻ v₀, f (v₀, v₁, y) := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ),
    lintegral_prod_symm' (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ × ℝ))) _ hf,
    Measure.volume_eq_prod ℝ ℝ,
    lintegral_prod_symm' (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      _ hf.lintegral_prod_left']

/-- Tonelli on `ℝ³ = ℝ × (ℝ × ℝ)` in the order `y` (outer), `v₀`, `v₁`
(inner). -/
private lemma lintegral_triple_v1 {f : ℝ × ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q : ℝ × ℝ × ℝ, f q = ∫⁻ y, ∫⁻ v₀, ∫⁻ v₁, f (v₀, v₁, y) := by
  rw [lintegral_triple_v0 hf]
  refine lintegral_congr fun y => ?_
  have hm : Measurable (Function.uncurry fun v₁ v₀ => f (v₀, v₁, y)) :=
    hf.comp (measurable_snd.prodMk (measurable_fst.prodMk measurable_const))
  exact lintegral_lintegral_swap hm.aemeasurable

/-- The `ℝ≥0∞` factorization of the resampling density. -/
private lemma ofReal_rd (φ : ℝ → ℝ) (v₀ v₁ y : ℝ) :
    ENNReal.ofReal (rd φ (v₀, v₁, y))
      = ENNReal.ofReal (jd φ v₀ y)
        * (ENNReal.ofReal (jd φ v₁ y)
          * ENNReal.ofReal (flowDensity φ y)⁻¹) := by
  change ENNReal.ofReal (jd φ v₀ y * jd φ v₁ y / flowDensity φ y) = _
  rw [div_eq_mul_inv, mul_assoc, ENNReal.ofReal_mul (jd_nonneg _ _ _),
    ENNReal.ofReal_mul (jd_nonneg _ _ _)]

private lemma ofReal_flowDensity_mul_inv {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    ENNReal.ofReal (flowDensity φ y) * ENNReal.ofReal (flowDensity φ y)⁻¹ = 1 := by
  have hp := lemma21_flowDensity_pos hφ y
  rw [← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one]

/-- The `v₁`-integral of the resampling density is the joint density at
`(v₀, y)`: `∫ ϱ(v₁)ϱ(y − φ v₁) dv₁ = p(y)` cancels the denominator. -/
private lemma lintegral_ofReal_rd_v1 {φ : ℝ → ℝ} (hφ : Measurable φ)
    (v₀ y : ℝ) :
    ∫⁻ v₁, ENNReal.ofReal (rd φ (v₀, v₁, y)) = ENNReal.ofReal (jd φ v₀ y) := by
  have hm2 : Measurable fun v : ℝ => ENNReal.ofReal (jd φ v y) :=
    (measurable_jd_left hφ y).ennreal_ofReal
  have hm : Measurable fun v : ℝ => ENNReal.ofReal (jd φ v y)
      * ENNReal.ofReal (flowDensity φ y)⁻¹ := hm2.mul measurable_const
  simp only [ofReal_rd]
  rw [lintegral_const_mul _ hm, lintegral_mul_const _ hm2,
    lintegral_jd_left φ y hφ, ofReal_flowDensity_mul_inv hφ y, mul_one]

/-- The `v₀`-integral of the resampling density, with a `v₀`-independent
weight factored out. -/
private lemma lintegral_ofReal_rd_v0 {φ : ℝ → ℝ} (hφ : Measurable φ)
    (v₁ y : ℝ) :
    ∫⁻ v₀, ENNReal.ofReal (rd φ (v₀, v₁, y)) = ENNReal.ofReal (jd φ v₁ y) := by
  have hm2 : Measurable fun v : ℝ => ENNReal.ofReal (jd φ v y) :=
    (measurable_jd_left hφ y).ennreal_ofReal
  simp only [ofReal_rd]
  rw [lintegral_mul_const _ hm2, lintegral_jd_left φ y hφ, ← mul_assoc,
    mul_comm (ENNReal.ofReal (flowDensity φ y)), mul_assoc,
    ofReal_flowDensity_mul_inv hφ y, mul_one]

/-- `∫ p(y) dy = 1`: the flow density integrates to one. -/
private lemma lintegral_ofReal_flowDensity {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫⁻ y, ENNReal.ofReal (flowDensity φ y) = 1 := by
  have hswap : ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y)
      = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (jd φ v y) := by
    have hm : Measurable (Function.uncurry fun y v => ENNReal.ofReal (jd φ v y)) :=
      (measurable_jd hφ measurable_snd measurable_fst).ennreal_ofReal
    exact lintegral_lintegral_swap hm.aemeasurable
  calc ∫⁻ y, ENNReal.ofReal (flowDensity φ y)
      = ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y) := by
        exact lintegral_congr fun y => (lintegral_jd_left φ y hφ).symm
    _ = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (jd φ v y) := hswap
    _ = ∫⁻ v, ENNReal.ofReal (stdNormalPDF v) :=
        lintegral_congr fun v => lintegral_jd_right φ v
    _ = 1 := by
        simpa [stdNormalPDF] using
          lintegral_ofReal_gaussianPDFReal_sub (v := 1) one_ne_zero 0

/-- **Master Tonelli identity for the resampling measure**, `v₁` innermost. -/
private lemma lintegral_resampling_v1 {φ : ℝ → ℝ} (hφ : Measurable φ)
    {f : ℝ × ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q, f q ∂(resamplingMeasure φ)
      = ∫⁻ y, ∫⁻ v₀, ∫⁻ v₁,
          ENNReal.ofReal (rd φ (v₀, v₁, y)) * f (v₀, v₁, y) := by
  rw [resamplingMeasure_eq, lintegral_withDensity_eq_lintegral_mul _
    (measurable_rd hφ).ennreal_ofReal hf]
  simp only [Pi.mul_apply]
  exact lintegral_triple_v1 ((measurable_rd hφ).ennreal_ofReal.mul hf)

/-- **Master Tonelli identity for the resampling measure**, `v₀` innermost. -/
private lemma lintegral_resampling_v0 {φ : ℝ → ℝ} (hφ : Measurable φ)
    {f : ℝ × ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q, f q ∂(resamplingMeasure φ)
      = ∫⁻ y, ∫⁻ v₁, ∫⁻ v₀,
          ENNReal.ofReal (rd φ (v₀, v₁, y)) * f (v₀, v₁, y) := by
  rw [resamplingMeasure_eq, lintegral_withDensity_eq_lintegral_mul _
    (measurable_rd hφ).ennreal_ofReal hf]
  simp only [Pi.mul_apply]
  exact lintegral_triple_v0 ((measurable_rd hφ).ennreal_ofReal.mul hf)

/-- **v4 Lemma 2.6, well-posedness**: the resampling measure is a
probability measure. -/
theorem isProbabilityMeasure_resamplingMeasure {φ : ℝ → ℝ}
    (hφ : Measurable φ) : IsProbabilityMeasure (resamplingMeasure φ) := by
  constructor
  rw [← lintegral_one, lintegral_resampling_v1 hφ measurable_const]
  simp only [mul_one]
  calc ∫⁻ y, ∫⁻ v₀, ∫⁻ v₁, ENNReal.ofReal (rd φ (v₀, v₁, y))
      = ∫⁻ y, ∫⁻ v₀, ENNReal.ofReal (jd φ v₀ y) :=
        lintegral_congr fun y =>
          lintegral_congr fun v₀ => lintegral_ofReal_rd_v1 hφ v₀ y
    _ = ∫⁻ y, ENNReal.ofReal (flowDensity φ y) :=
        lintegral_congr fun y => lintegral_jd_left φ y hφ
    _ = 1 := lintegral_ofReal_flowDensity hφ

/-! ## (i) Exchangeability -/

private lemma rd_symm (φ : ℝ → ℝ) (v₀ v₁ y : ℝ) :
    rd φ (v₀, v₁, y) = rd φ (v₁, v₀, y) := by
  change jd φ v₀ y * jd φ v₁ y / flowDensity φ y
    = jd φ v₁ y * jd φ v₀ y / flowDensity φ y
  rw [mul_comm]

private lemma measurable_exch :
    Measurable fun q : ℝ × ℝ × ℝ => (q.2.1, q.1, q.2.2) :=
  measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)

/-- **v4 Lemma 2.6 (i)**: the triples `(V⁰, V¹, Y)` and `(V¹, V⁰, Y)` have
the same law — the resampling measure is invariant under exchanging the two
replicas. -/
theorem resamplingMeasure_map_swap {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => (q.2.1, q.1, q.2.2))
        (resamplingMeasure φ) = resamplingMeasure φ := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hcomp : Measurable fun q : ℝ × ℝ × ℝ => f (q.2.1, q.1, q.2.2) :=
    hf.comp measurable_exch
  rw [lintegral_map hf measurable_exch, lintegral_resampling_v1 hφ hcomp,
    lintegral_resampling_v0 hφ hf]
  exact lintegral_congr fun y => lintegral_congr fun a =>
    lintegral_congr fun b => by rw [rd_symm]

/-! ## (ii) The two-dimensional marginals -/

private lemma lintegral_joint_withDensity {φ : ℝ → ℝ} (hφ : Measurable φ)
    {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂(volume.withDensity fun r : ℝ × ℝ =>
        ENNReal.ofReal (stdNormalPDF r.1 * stdNormalPDF (r.2 - φ r.1)))
      = ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y) * f (v, y) := by
  have hd : Measurable fun r : ℝ × ℝ =>
      ENNReal.ofReal (stdNormalPDF r.1 * stdNormalPDF (r.2 - φ r.1)) :=
    (measurable_jd hφ measurable_fst measurable_snd).ennreal_ofReal
  have hmul : Measurable fun r : ℝ × ℝ => ENNReal.ofReal (jd φ r.1 r.2) * f r :=
    ((measurable_jd hφ measurable_fst measurable_snd).ennreal_ofReal).mul hf
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf]
  simp only [Pi.mul_apply, jd_apply]
  rw [Measure.volume_eq_prod ℝ ℝ,
    lintegral_prod_symm' (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      _ hmul]

/-- **v4 Lemma 2.6 (ii)**: the `(V¹, Y)` marginal of the resampling measure
is the joint law of `(V, Y)`, in density form `ϱ(v)·ϱ(y − φ(v))`. -/
theorem resamplingMeasure_map_snd {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2)) (resamplingMeasure φ)
      = volume.withDensity fun r : ℝ × ℝ =>
          ENNReal.ofReal (stdNormalPDF r.1 * stdNormalPDF (r.2 - φ r.1)) := by
  have hg : Measurable fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2) :=
    measurable_snd.fst.prodMk measurable_snd.snd
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hcomp : Measurable fun q : ℝ × ℝ × ℝ => f (q.2.1, q.2.2) := hf.comp hg
  rw [lintegral_map hf hg, lintegral_resampling_v0 hφ hcomp,
    lintegral_joint_withDensity hφ hf]
  refine lintegral_congr fun y => lintegral_congr fun v₁ => ?_
  dsimp only
  have hm : Measurable fun v₀ : ℝ => ENNReal.ofReal (rd φ (v₀, v₁, y)) :=
    ((measurable_rd hφ).comp
      (measurable_id.prodMk measurable_const)).ennreal_ofReal
  rw [lintegral_mul_const _ hm, lintegral_ofReal_rd_v0 hφ v₁ y]

/-- **v4 Lemma 2.6 (ii)**, companion form: the `(V⁰, Y)` marginal of the
resampling measure is the same joint law (`V⁰ = V` by construction). -/
theorem resamplingMeasure_map_fst {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2)) (resamplingMeasure φ)
      = volume.withDensity fun r : ℝ × ℝ =>
          ENNReal.ofReal (stdNormalPDF r.1 * stdNormalPDF (r.2 - φ r.1)) := by
  have hg : Measurable fun q : ℝ × ℝ × ℝ => (q.1, q.2.2) :=
    measurable_fst.prodMk measurable_snd.snd
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hcomp : Measurable fun q : ℝ × ℝ × ℝ => f (q.1, q.2.2) := hf.comp hg
  rw [lintegral_map hf hg, lintegral_resampling_v1 hφ hcomp,
    lintegral_joint_withDensity hφ hf]
  refine lintegral_congr fun y => lintegral_congr fun v₀ => ?_
  dsimp only
  have hm : Measurable fun v₁ : ℝ => ENNReal.ofReal (rd φ (v₀, v₁, y)) :=
    ((measurable_rd hφ).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))).ennreal_ofReal
  rw [lintegral_mul_const _ hm, lintegral_ofReal_rd_v1 hφ v₀ y]

/-! ## One-dimensional marginals and first moments -/

private lemma lintegral_gaussianReal_std {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v ∂(gaussianReal 0 1)
      = ∫⁻ v, ENNReal.ofReal (stdNormalPDF v) * f v := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hf]
  exact lintegral_congr fun v => rfl

/-- The replica `V¹` is standard normal under the resampling measure (the
`V¹`-marginal of v4 Lemma 2.6 (ii)). -/
theorem resamplingMeasure_map_v1 {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => q.2.1) (resamplingMeasure φ)
      = gaussianReal 0 1 := by
  have hg : Measurable fun q : ℝ × ℝ × ℝ => q.2.1 := measurable_snd.fst
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hcomp : Measurable fun q : ℝ × ℝ × ℝ => f q.2.1 := hf.comp hg
  have hswap : ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y) * f v
      = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (jd φ v y) * f v := by
    have hm : Measurable (Function.uncurry fun y v =>
        ENNReal.ofReal (jd φ v y) * f v) :=
      ((measurable_jd hφ measurable_snd measurable_fst).ennreal_ofReal).mul
        (hf.comp measurable_snd)
    exact lintegral_lintegral_swap hm.aemeasurable
  rw [lintegral_map hf hg, lintegral_resampling_v0 hφ hcomp,
    lintegral_gaussianReal_std hf]
  calc ∫⁻ y, ∫⁻ v₁, ∫⁻ v₀, ENNReal.ofReal (rd φ (v₀, v₁, y)) * f v₁
      = ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y) * f v := by
        refine lintegral_congr fun y => lintegral_congr fun v₁ => ?_
        have hm : Measurable fun v₀ : ℝ => ENNReal.ofReal (rd φ (v₀, v₁, y)) :=
          ((measurable_rd hφ).comp
            (measurable_id.prodMk measurable_const)).ennreal_ofReal
        rw [lintegral_mul_const _ hm, lintegral_ofReal_rd_v0 hφ v₁ y]
    _ = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (jd φ v y) * f v := hswap
    _ = ∫⁻ v, ENNReal.ofReal (stdNormalPDF v) * f v := by
        refine lintegral_congr fun v => ?_
        rw [lintegral_mul_const _ (measurable_jd_right hφ v).ennreal_ofReal,
          lintegral_jd_right φ v]

/-- `V⁰ = V` is standard normal under the resampling measure. -/
theorem resamplingMeasure_map_v0 {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => q.1) (resamplingMeasure φ)
      = gaussianReal 0 1 := by
  have hg : Measurable fun q : ℝ × ℝ × ℝ => q.1 := measurable_fst
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hcomp : Measurable fun q : ℝ × ℝ × ℝ => f q.1 := hf.comp hg
  have hswap : ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y) * f v
      = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (jd φ v y) * f v := by
    have hm : Measurable (Function.uncurry fun y v =>
        ENNReal.ofReal (jd φ v y) * f v) :=
      ((measurable_jd hφ measurable_snd measurable_fst).ennreal_ofReal).mul
        (hf.comp measurable_snd)
    exact lintegral_lintegral_swap hm.aemeasurable
  rw [lintegral_map hf hg, lintegral_resampling_v1 hφ hcomp,
    lintegral_gaussianReal_std hf]
  calc ∫⁻ y, ∫⁻ v₀, ∫⁻ v₁, ENNReal.ofReal (rd φ (v₀, v₁, y)) * f v₀
      = ∫⁻ y, ∫⁻ v, ENNReal.ofReal (jd φ v y) * f v := by
        refine lintegral_congr fun y => lintegral_congr fun v₀ => ?_
        have hm : Measurable fun v₁ : ℝ => ENNReal.ofReal (rd φ (v₀, v₁, y)) :=
          ((measurable_rd hφ).comp (measurable_const.prodMk
            (measurable_id.prodMk measurable_const))).ennreal_ofReal
        rw [lintegral_mul_const _ hm, lintegral_ofReal_rd_v1 hφ v₀ y]
    _ = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (jd φ v y) * f v := hswap
    _ = ∫⁻ v, ENNReal.ofReal (stdNormalPDF v) * f v := by
        refine lintegral_congr fun v => ?_
        rw [lintegral_mul_const _ (measurable_jd_right hφ v).ennreal_ofReal,
          lintegral_jd_right φ v]

/-- The order flow `Y` has law `p(y) dy` under the resampling measure
(v4 Lemma 2.1's law clause, seen on `μ₃`). -/
theorem resamplingMeasure_map_y {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => q.2.2) (resamplingMeasure φ)
      = volume.withDensity fun y => ENNReal.ofReal (flowDensity φ y) := by
  have hg : Measurable fun q : ℝ × ℝ × ℝ => q.2.2 := measurable_snd.snd
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hcomp : Measurable fun q : ℝ × ℝ × ℝ => f q.2.2 := hf.comp hg
  rw [lintegral_map hf hg, lintegral_resampling_v1 hφ hcomp,
    lintegral_withDensity_eq_lintegral_mul _
      ((continuous_flowDensity hφ).measurable.ennreal_ofReal) hf]
  simp only [Pi.mul_apply]
  refine lintegral_congr fun y => ?_
  have hm : Measurable fun v₀ : ℝ => ENNReal.ofReal (jd φ v₀ y) :=
    (measurable_jd_left hφ y).ennreal_ofReal
  calc ∫⁻ v₀, ∫⁻ v₁, ENNReal.ofReal (rd φ (v₀, v₁, y)) * f y
      = ∫⁻ v₀, ENNReal.ofReal (jd φ v₀ y) * f y := by
        refine lintegral_congr fun v₀ => ?_
        have hm' : Measurable fun v₁ : ℝ => ENNReal.ofReal (rd φ (v₀, v₁, y)) :=
          ((measurable_rd hφ).comp (measurable_const.prodMk
            (measurable_id.prodMk measurable_const))).ennreal_ofReal
        rw [lintegral_mul_const _ hm', lintegral_ofReal_rd_v1 hφ v₀ y]
    _ = ENNReal.ofReal (flowDensity φ y) * f y := by
        rw [lintegral_mul_const _ hm, lintegral_jd_left φ y hφ]

/-- **v4 Lemma 2.6, integrability**: the replica `V¹` has a finite first
moment under the resampling measure. -/
theorem integrable_v1_resampling {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => q.2.1) (resamplingMeasure φ) := by
  have h : Integrable id (Measure.map (fun q : ℝ × ℝ × ℝ => q.2.1)
      (resamplingMeasure φ)) := by
    rw [resamplingMeasure_map_v1 hφ]
    exact integrable_id_gaussianReal 0 1
  exact h.comp_measurable measurable_snd.fst

/-- `V⁰ = V` has a finite first moment under the resampling measure. -/
theorem integrable_v0_resampling {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => q.1) (resamplingMeasure φ) := by
  have h : Integrable id (Measure.map (fun q : ℝ × ℝ × ℝ => q.1)
      (resamplingMeasure φ)) := by
    rw [resamplingMeasure_map_v0 hφ]
    exact integrable_id_gaussianReal 0 1
  exact h.comp_measurable measurable_fst

/-- `P(Y)` is integrable under the resampling measure (it is `L²` by
Lemma 2.2 and `μ₃` is a probability measure). -/
theorem integrable_inverseRegression_resampling {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => inverseRegression φ q.2.2)
      (resamplingMeasure φ) := by
  have hlaw : Measure.map (fun q : ℝ × ℝ × ℝ => q.2.2) (resamplingMeasure φ)
      = Measure.map (stdModel.orderFlow φ) stdModel.μ := by
    rw [resamplingMeasure_map_y hφ, stdModel.map_orderFlow hφ]
    exact congrArg _ (funext fun y => congrArg _ (stdModel_flowPDF φ y).symm)
  have hPY : Integrable (fun ω => inverseRegression φ (stdModel.orderFlow φ ω))
      stdModel.μ := (lemma22_memLp_two hφ).integrable one_le_two
  have h : Integrable (inverseRegression φ)
      (Measure.map (fun q : ℝ × ℝ × ℝ => q.2.2) (resamplingMeasure φ)) := by
    rw [hlaw]
    exact (integrable_map_measure
      (measurable_inverseRegression hφ).aestronglyMeasurable
      (stdModel.measurable_orderFlow hφ).aemeasurable).mpr hPY
  exact h.comp_measurable measurable_snd.snd

/-! ## Bochner integration against the resampling measure -/

private lemma integrable_id_mul_jd {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => v * jd φ v y) := by
  have hb : Integrable (fun v => |v * gaussianPDFReal 0 1 v|
      * (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹) (volume : Measure ℝ) :=
    ((integrable_id_mul_gaussianPDFReal 0 1).abs).mul_const _
  refine Integrable.mono' hb
    (measurable_id.mul (measurable_jd hφ measurable_id measurable_const)).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  have hnn : (0:ℝ) ≤ gaussianPDFReal 0 1 (y - φ v) := gaussianPDFReal_nonneg _ _ _
  rw [Real.norm_eq_abs]
  calc |v * jd φ v y|
      = |v * gaussianPDFReal 0 1 v| * gaussianPDFReal 0 1 (y - φ v) := by
        rw [jd, stdNormalPDF, ← mul_assoc, abs_mul, abs_of_nonneg hnn]
    _ ≤ |v * gaussianPDFReal 0 1 v| * (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left (gaussianPDFReal_le _ _ _) (abs_nonneg _)

/-- The flow numerator in flat form: `∫ v ϱ(v) ϱ(y − φ v) dv = P(y)·p(y)`. -/
private lemma integral_id_mul_jd {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    ∫ v, v * jd φ v y = inverseRegression φ y * flowDensity φ y := by
  have h : ∫ v, v * jd φ v y
      = ∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1 := by
    rw [integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [jd, stdNormalPDF, smul_eq_mul]
    ring
  rw [h, inverseRegression, div_mul_cancel₀ _ (lemma21_flowDensity_pos hφ y).ne']

/-- The Bayes-numerator kernel `v ↦ v·ϱ(v)·ϱ(y − φ(v))` is Lebesgue
integrable — so the flat numerator below is a genuine Bochner integral and
the identities of this file are not vacuous. -/
theorem integrable_bayesNumerator_kernel {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    Integrable (fun v => v * (stdNormalPDF v * stdNormalPDF (y - φ v)))
      (volume : Measure ℝ) :=
  integrable_id_mul_jd hφ y

/-- The flat (Lebesgue) form of the Bayes numerator:
`∫ v·ϱ(v)·ϱ(y − φ(v)) dv = P(y)·p(y)` (v4 §3, the quotient defining `P`). -/
theorem integral_bayesNumerator_kernel {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    ∫ v, v * (stdNormalPDF v * stdNormalPDF (y - φ v))
      = inverseRegression φ y * flowDensity φ y :=
  integral_id_mul_jd hφ y

private lemma integral_resamplingMeasure {φ : ℝ → ℝ} (hφ : Measurable φ)
    (F : ℝ × ℝ × ℝ → ℝ) :
    ∫ q, F q ∂(resamplingMeasure φ) = ∫ q, rd φ q * F q := by
  rw [resamplingMeasure_eq, integral_withDensity_eq_integral_toReal_smul
    (measurable_rd hφ).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (rd_nonneg hφ q)]

private lemma integrable_rd_mul {φ : ℝ → ℝ} (hφ : Measurable φ)
    {F : ℝ × ℝ × ℝ → ℝ} (hF : Integrable F (resamplingMeasure φ)) :
    Integrable (fun q => rd φ q * F q) (volume : Measure (ℝ × ℝ × ℝ)) := by
  rw [resamplingMeasure_eq] at hF
  have h := (integrable_withDensity_iff (measurable_rd hφ).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hF
  refine h.congr (ae_of_all _ fun q => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (rd_nonneg hφ q), mul_comm]

/-- Fubini on `ℝ³`, `v₁` innermost. -/
private lemma integral_triple_v1 {G : ℝ × ℝ × ℝ → ℝ}
    (hG : Integrable G (volume : Measure (ℝ × ℝ × ℝ))) :
    ∫ q, G q = ∫ v₀, ∫ y, ∫ v₁, G (v₀, v₁, y) := by
  have hG' : Integrable G
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rwa [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), integral_prod _ hG']
  refine integral_congr_ae ?_
  filter_upwards [hG'.prod_right_ae] with v₀ hv₀
  have hv₀' : Integrable (fun s : ℝ × ℝ => G (v₀, s))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rwa [← Measure.volume_eq_prod ℝ ℝ]
  rw [Measure.volume_eq_prod ℝ ℝ, integral_prod_symm _ hv₀']

/-- The inner `v₁`-integral against the resampling density, with a
`v₁`-independent factor: `∫ ϱ(v₁)ϱ(y − φ v₁) dv₁ = p(y)` cancels. -/
private lemma integral_rd_v1_const {φ : ℝ → ℝ} (hφ : Measurable φ)
    (v₀ y c : ℝ) :
    ∫ v₁, rd φ (v₀, v₁, y) * c = jd φ v₀ y * c := by
  have hpne : flowDensity φ y ≠ 0 := (lemma21_flowDensity_pos hφ y).ne'
  have h1 : ∀ v₁ : ℝ, rd φ (v₀, v₁, y) * c
      = jd φ v₀ y / flowDensity φ y * c * jd φ v₁ y := by
    intro v₁
    change jd φ v₀ y * jd φ v₁ y / flowDensity φ y * c = _
    ring
  simp only [h1]
  rw [integral_const_mul, integral_jd_left φ y, div_mul_eq_mul_div,
    div_mul_cancel₀ _ hpne]

/-- The inner `v₁`-integral against the resampling density, weighted by
`v₁`: `∫ v₁ ϱ(v₁)ϱ(y − φ v₁) dv₁ = P(y)·p(y)`. -/
private lemma integral_rd_v1_id {φ : ℝ → ℝ} (hφ : Measurable φ)
    (v₀ y c : ℝ) :
    ∫ v₁, rd φ (v₀, v₁, y) * (v₁ * c)
      = jd φ v₀ y * (inverseRegression φ y * c) := by
  have hpne : flowDensity φ y ≠ 0 := (lemma21_flowDensity_pos hφ y).ne'
  have h1 : ∀ v₁ : ℝ, rd φ (v₀, v₁, y) * (v₁ * c)
      = jd φ v₀ y / flowDensity φ y * c * (v₁ * jd φ v₁ y) := by
    intro v₁
    change jd φ v₀ y * jd φ v₁ y / flowDensity φ y * (v₁ * c) = _
    ring
  simp only [h1]
  rw [integral_const_mul, integral_id_mul_jd hφ y]
  field_simp

/-! ## (iii) The conditional expectation of the replica given `(V⁰, Y)` -/

/-- **v4 Lemma 2.6 (iii)**, test-function form: for every bounded Borel
`g : ℝ × ℝ → ℝ`,
`E[V¹·g(V⁰, Y)] = E[P(Y)·g(V⁰, Y)]`,
which is `E[V¹ ∣ Y, V⁰] = P(Y)` in integrated form. -/
theorem integral_v1_mul_eq_inverseRegression {φ : ℝ → ℝ} (hφ : Measurable φ)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hgb : ∀ r, |g r| ≤ C) :
    ∫ q, q.2.1 * g (q.1, q.2.2) ∂(resamplingMeasure φ)
      = ∫ q, inverseRegression φ q.2.2 * g (q.1, q.2.2)
          ∂(resamplingMeasure φ) := by
  have hgm : Measurable fun q : ℝ × ℝ × ℝ => g (q.1, q.2.2) :=
    hg.comp (measurable_fst.prodMk measurable_snd.snd)
  have hbound : ∀ᵐ q ∂(resamplingMeasure φ), ‖g (q.1, q.2.2)‖ ≤ C :=
    ae_of_all _ fun q => hgb _
  have hL : Integrable (fun q : ℝ × ℝ × ℝ => q.2.1 * g (q.1, q.2.2))
      (resamplingMeasure φ) :=
    (integrable_v1_resampling hφ).mul_bdd hgm.aestronglyMeasurable hbound
  have hR : Integrable
      (fun q : ℝ × ℝ × ℝ => inverseRegression φ q.2.2 * g (q.1, q.2.2))
      (resamplingMeasure φ) :=
    (integrable_inverseRegression_resampling hφ).mul_bdd hgm.aestronglyMeasurable hbound
  rw [integral_resamplingMeasure hφ, integral_resamplingMeasure hφ,
    integral_triple_v1 (integrable_rd_mul hφ hL),
    integral_triple_v1 (integrable_rd_mul hφ hR)]
  refine integral_congr_ae (ae_of_all _ fun v₀ => ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [integral_rd_v1_id hφ v₀ y (g (v₀, y)),
    integral_rd_v1_const hφ v₀ y (inverseRegression φ y * g (v₀, y))]

/-! ## (iv) The conditional expectation of the replica given `V⁰` -/

private lemma integral_jointMeasure {φ : ℝ → ℝ} (hφ : Measurable φ)
    (F : ℝ × ℝ → ℝ) :
    ∫ r, F r ∂(volume.withDensity fun r : ℝ × ℝ =>
        ENNReal.ofReal (stdNormalPDF r.1 * stdNormalPDF (r.2 - φ r.1)))
      = ∫ r, jd φ r.1 r.2 * F r := by
  simp only [jd_apply]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_jd hφ measurable_fst measurable_snd).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (jd_nonneg φ r.1 r.2)]

private lemma integrable_jd_mul {φ : ℝ → ℝ} (hφ : Measurable φ)
    {F : ℝ × ℝ → ℝ}
    (hF : Integrable F (volume.withDensity fun r : ℝ × ℝ =>
      ENNReal.ofReal (stdNormalPDF r.1 * stdNormalPDF (r.2 - φ r.1)))) :
    Integrable (fun r => jd φ r.1 r.2 * F r) (volume : Measure (ℝ × ℝ)) := by
  simp only [jd_apply] at hF
  have h := (integrable_withDensity_iff
    (measurable_jd hφ measurable_fst measurable_snd).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hF
  refine h.congr (ae_of_all _ fun r => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (jd_nonneg φ r.1 r.2), mul_comm]

private lemma integral_pair {G : ℝ × ℝ → ℝ}
    (hG : Integrable G (volume : Measure (ℝ × ℝ))) :
    ∫ r, G r = ∫ v, ∫ y, G (v, y) := by
  have hG' : Integrable G ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rwa [← Measure.volume_eq_prod ℝ ℝ]
  rw [Measure.volume_eq_prod ℝ ℝ, integral_prod _ hG']

/-- **v4 Lemma 2.6 (iv)**, test-function form: for every bounded Borel
`g : ℝ → ℝ`,
`E[V¹·g(V⁰)] = E[F(φ(V))·g(V)]`,
which is `E[V¹ ∣ V⁰] = F(φ(V⁰))` in integrated form. -/
theorem integral_v1_mul_eq_gaussianSmoothing {φ : ℝ → ℝ} (hφ : Measurable φ)
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hgb : ∀ v, |g v| ≤ C) :
    ∫ q, q.2.1 * g q.1 ∂(resamplingMeasure φ)
      = ∫ v, gaussianSmoothing φ (φ v) * g v ∂(gaussianReal 0 1) := by
  have hg' : Measurable fun r : ℝ × ℝ => g r.1 := hg.comp measurable_fst
  -- Step 1: replace `V¹` by `P(Y)` using (iii).
  have step1 := integral_v1_mul_eq_inverseRegression hφ (g := fun r : ℝ × ℝ => g r.1) hg'
    (C := C) (fun r => hgb r.1)
  -- Step 2: push forward to the `(V⁰, Y)` marginal.
  have hmapfst : Measurable fun q : ℝ × ℝ × ℝ => (q.1, q.2.2) :=
    measurable_fst.prodMk measurable_snd.snd
  have hPg : Measurable fun r : ℝ × ℝ => inverseRegression φ r.2 * g r.1 :=
    ((measurable_inverseRegression hφ).comp measurable_snd).mul hg'
  have hRq : Integrable
      (fun q : ℝ × ℝ × ℝ => inverseRegression φ q.2.2 * g q.1)
      (resamplingMeasure φ) :=
    (integrable_inverseRegression_resampling hφ).mul_bdd
      (hg.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun q => hgb q.1)
  have hRmap : Integrable (fun r : ℝ × ℝ => inverseRegression φ r.2 * g r.1)
      (Measure.map (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2))
        (resamplingMeasure φ)) :=
    (integrable_map_measure hPg.aestronglyMeasurable
      hmapfst.aemeasurable).mpr hRq
  have step2 : ∫ q, inverseRegression φ q.2.2 * g q.1 ∂(resamplingMeasure φ)
      = ∫ r, inverseRegression φ r.2 * g r.1
          ∂(Measure.map (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2))
            (resamplingMeasure φ)) :=
    (integral_map hmapfst.aemeasurable hPg.aestronglyMeasurable).symm
  rw [resamplingMeasure_map_fst hφ] at step2 hRmap
  -- Step 3: Fubini on the `(v, y)` plane, integrating `y` out.
  have hint : Integrable
      (fun r : ℝ × ℝ => jd φ r.1 r.2 * (inverseRegression φ r.2 * g r.1))
      (volume : Measure (ℝ × ℝ)) := integrable_jd_mul hφ hRmap
  rw [step1, step2, integral_jointMeasure hφ, integral_pair hint]
  -- Step 4: the inner `y`-integral is the convolution form of `F`.
  have hinner : ∀ v : ℝ,
      ∫ y, jd φ v y * (inverseRegression φ y * g v)
        = stdNormalPDF v * (gaussianSmoothing φ (φ v) * g v) := by
    intro v
    have hrw : ∀ y : ℝ, jd φ v y * (inverseRegression φ y * g v)
        = stdNormalPDF v * g v
          * (inverseRegression φ y * stdNormalPDF (y - φ v)) := by
      intro y
      change stdNormalPDF v * stdNormalPDF (y - φ v)
        * (inverseRegression φ y * g v) = _
      ring
    simp only [hrw]
    rw [integral_const_mul, ← gaussianSmoothing_eq_convolution hφ (φ v)]
    ring
  simp only [hinner]
  rw [integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [smul_eq_mul, stdNormalPDF]

/-! ## Moment identities for v4 Proposition 5.1 -/

/-- The replica identity in the form needed by v4 (5.2): for every bounded
Borel `k`, `E[V¹·k(φ(V⁰))] = E[F(φ(V))·k(φ(V))]`. -/
theorem integral_v1_mul_comp_eq_gaussianSmoothing {φ : ℝ → ℝ}
    (hφ : Measurable φ) {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ}
    (hkb : ∀ x, |k x| ≤ C) :
    ∫ q, q.2.1 * k (φ q.1) ∂(resamplingMeasure φ)
      = ∫ v, gaussianSmoothing φ (φ v) * k (φ v) ∂(gaussianReal 0 1) :=
  integral_v1_mul_eq_gaussianSmoothing hφ (hk.comp hφ) (C := C)
    fun v => hkb (φ v)

/-- Fubini on `ℝ³`, `y` outermost and `v₀` innermost. -/
private lemma integral_triple_v0 {G : ℝ × ℝ × ℝ → ℝ}
    (hG : Integrable G (volume : Measure (ℝ × ℝ × ℝ))) :
    ∫ q, G q = ∫ y, ∫ v₁, ∫ v₀, G (v₀, v₁, y) := by
  have hG' : Integrable G
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rwa [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  have hH : Integrable (fun s : ℝ × ℝ => ∫ v₀, G (v₀, s))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have h := hG'.integral_prod_right
    rwa [Measure.volume_eq_prod ℝ ℝ] at h
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), integral_prod_symm _ hG',
    Measure.volume_eq_prod ℝ ℝ, integral_prod_symm _ hH]

private lemma memLp_two_v0 {φ : ℝ → ℝ} (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => q.1) 2 (resamplingMeasure φ) := by
  have h : MemLp id 2 (Measure.map (fun q : ℝ × ℝ × ℝ => q.1)
      (resamplingMeasure φ)) := by
    rw [resamplingMeasure_map_v0 hφ]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    measurable_fst.aemeasurable).mp h

private lemma memLp_two_v1 {φ : ℝ → ℝ} (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => q.2.1) 2 (resamplingMeasure φ) := by
  have h : MemLp id 2 (Measure.map (fun q : ℝ × ℝ × ℝ => q.2.1)
      (resamplingMeasure φ)) := by
    rw [resamplingMeasure_map_v1 hφ]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    measurable_snd.fst.aemeasurable).mp h

/-- The product `V⁰·V¹` is integrable under the resampling measure (both
replicas are standard normal, hence `L²`). -/
theorem integrable_v0_mul_v1_resampling {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => q.1 * q.2.1) (resamplingMeasure φ) :=
  (memLp_two_v0 hφ).integrable_mul (memLp_two_v1 hφ)

/-- The replica covariance identity `E[V⁰·V¹] = E[P(Y)²]` (the `Γ`-side
bookkeeping of v4 Proposition 5.1). -/
theorem integral_v0_mul_v1_resampling {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ q, q.1 * q.2.1 ∂(resamplingMeasure φ)
      = ∫ y, inverseRegression φ y ^ 2 * flowDensity φ y := by
  rw [integral_resamplingMeasure hφ,
    integral_triple_v0 (integrable_rd_mul hφ (integrable_v0_mul_v1_resampling hφ))]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  have hin : ∀ v₁ : ℝ, ∫ v₀, rd φ (v₀, v₁, y) * (v₀ * v₁)
      = inverseRegression φ y * (v₁ * jd φ v₁ y) := by
    intro v₁
    have h : ∀ v₀ : ℝ, rd φ (v₀, v₁, y) * (v₀ * v₁)
        = rd φ (v₁, v₀, y) * (v₀ * v₁) := fun v₀ => by rw [rd_symm]
    simp only [h]
    rw [integral_rd_v1_id hφ v₁ y v₁]
    ring
  simp only [hin]
  rw [integral_const_mul, integral_id_mul_jd hφ y]
  ring

/-! ## (R2b) `F(φ(V)) = E[E[V ∣ Y] ∣ V]` on the normalised model -/

private lemma continuous_gaussianSmoothing {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Continuous (gaussianSmoothing φ) :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_gaussianSmoothing hφ x).continuousAt

/-- `F(φ(V)) ∈ L¹`: the Gaussian smoothing along the strategy is integrable
against the prior (it is a partial integral of `P(Y) ∈ L¹`). -/
theorem integrable_gaussianSmoothing_comp {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Integrable (fun v => gaussianSmoothing φ (φ v)) (gaussianReal 0 1) := by
  have hPY : Integrable (fun ω : ℝ × ℝ => inverseRegression φ (φ ω.1 + ω.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (lemma22_memLp_two hφ).integrable one_le_two
  exact hPY.integral_prod_left

/-- **v4 Lemma 2.3, bookkeeping clause (blueprint node R2b)**: on the
normalised model, `F(φ(V)) = E[E[V ∣ Y] ∣ V]` almost surely — the tower
step that feeds v4 Proposition 5.1 through Lemma 2.6 (iv). -/
theorem gaussianSmoothing_comp_ae_eq_condExp_condExp {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    (fun ω : ℝ × ℝ => gaussianSmoothing φ (φ (stdModel.V ω)))
      =ᵐ[stdModel.μ]
        condExp (MeasurableSpace.comap stdModel.V inferInstance) stdModel.μ
          (condExp (stdModel.flowSigma φ) stdModel.μ stdModel.V) := by
  have hm : MeasurableSpace.comap stdModel.V inferInstance
      ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) := stdModel.hV.comap_le
  have hPY : Integrable (fun ω : ℝ × ℝ => inverseRegression φ (φ ω.1 + ω.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (lemma22_memLp_two hφ).integrable one_le_two
  have hFint := integrable_gaussianSmoothing_comp hφ
  have hFmeas : Measurable fun v => gaussianSmoothing φ (φ v) :=
    (continuous_gaussianSmoothing hφ).measurable.comp hφ
  have hmapfst : Measure.map Prod.fst
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 :=
    MeasureTheory.measurePreserving_fst.map_eq
  have hFcomp : Integrable (fun ω : ℝ × ℝ => gaussianSmoothing φ (φ ω.1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have h : Integrable (fun v => gaussianSmoothing φ (φ v))
        (Measure.map Prod.fst
          ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
      rw [hmapfst]; exact hFint
    exact h.comp_measurable measurable_fst
  have hmain : (fun ω : ℝ × ℝ => gaussianSmoothing φ (φ ω.1))
      =ᵐ[(gaussianReal 0 1).prod (gaussianReal 0 1)]
        condExp (MeasurableSpace.comap stdModel.V inferInstance)
          ((gaussianReal 0 1).prod (gaussianReal 0 1))
          (fun ω : ℝ × ℝ => inverseRegression φ (φ ω.1 + ω.2)) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hPY
      (fun s _ _ => hFcomp.integrableOn) ?_ ?_
    · rintro s ⟨A, hA, rfl⟩ -
      have hAind : Measurable (A.indicator fun _ => (1 : ℝ)) :=
        measurable_const.indicator hA
      have hAbd : ∀ v : ℝ, ‖A.indicator (fun _ => (1 : ℝ)) v‖ ≤ 1 := by
        intro v
        by_cases hv : v ∈ A
        · rw [Set.indicator_of_mem hv]; norm_num
        · rw [Set.indicator_of_notMem hv]; norm_num
      have hind : ∀ h : ℝ × ℝ → ℝ, ∀ ω : ℝ × ℝ,
          (stdModel.V ⁻¹' A).indicator h ω
            = A.indicator (fun _ => (1 : ℝ)) ω.1 * h ω := by
        intro h ω
        by_cases hx : ω.1 ∈ A
        · rw [Set.indicator_of_mem (show ω ∈ stdModel.V ⁻¹' A from hx),
            Set.indicator_of_mem hx, one_mul]
        · rw [Set.indicator_of_notMem (show ω ∉ stdModel.V ⁻¹' A from hx),
            Set.indicator_of_notMem hx, zero_mul]
      have hsm : MeasurableSet (stdModel.V ⁻¹' A) := stdModel.hV hA
      have hPint : Integrable (fun ω : ℝ × ℝ =>
          A.indicator (fun _ => (1 : ℝ)) ω.1 * inverseRegression φ (φ ω.1 + ω.2))
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
        hPY.bdd_mul (hAind.comp measurable_fst).aestronglyMeasurable
          (ae_of_all _ fun ω => hAbd ω.1)
      calc ∫ ω in stdModel.V ⁻¹' A, gaussianSmoothing φ (φ ω.1)
            ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
          = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω.1
              * gaussianSmoothing φ (φ ω.1)
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rw [← integral_indicator hsm]
            exact integral_congr_ae (ae_of_all _ (hind _))
        _ = ∫ v, A.indicator (fun _ => (1 : ℝ)) v * gaussianSmoothing φ (φ v)
              ∂(gaussianReal 0 1) := by
            have hfm : AEStronglyMeasurable
                (fun v => A.indicator (fun _ => (1 : ℝ)) v
                  * gaussianSmoothing φ (φ v))
                (Measure.map Prod.fst
                  ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
              rw [hmapfst]
              exact (hAind.mul hFmeas).aestronglyMeasurable
            have h := integral_map
              (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
              measurable_fst.aemeasurable hfm
            rw [hmapfst] at h
            exact h.symm
        _ = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω.1
              * inverseRegression φ (φ ω.1 + ω.2)
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rw [integral_prod _ hPint]
            refine integral_congr_ae (ae_of_all _ fun v => ?_)
            dsimp only
            rw [integral_const_mul]
            rfl
        _ = ∫ ω in stdModel.V ⁻¹' A, inverseRegression φ (φ ω.1 + ω.2)
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rw [← integral_indicator hsm]
            exact (integral_congr_ae (ae_of_all _ (hind _))).symm
    · have hmeas : Measurable[MeasurableSpace.comap stdModel.V inferInstance]
          fun ω : ℝ × ℝ => gaussianSmoothing φ (φ ω.1) :=
        hFmeas.comp (Measurable.of_comap_le le_rfl)
      exact hmeas.stronglyMeasurable.aestronglyMeasurable
  exact hmain.trans (condExp_congr_ae (lemma21_isPricingRule hφ).ae_eq_condExp)

end KyleUniqueness




