/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.PosteriorDeriv

/-!
# The posterior `π_y`, the covariance form of `P′`, and `F′ > 0`

Blueprint nodes **A1b**, the remainder of **D1**, and **D2**; paper
arXiv:2607.23585 **v4** (2026-08-20): Lemma 2.1 (joint density of `(V, Y)`),
§2.2 (definition of `π_y`), and Lemma 2.5 (= v3 Lemma 4.1), eqs. (2.7) and
(2.8).

## Contents

* **Node A1b** (v4 Lemma 2.1, first clause) — `map_value_orderFlow`: the
  joint law of `(V, Y) = (V, φ(V) + U)` on the normalised model is
  Lebesgue measure on `ℝ × ℝ` weighted by `ϱ(v)·ϱ(y − φ(v))`, with
  `stdModel` packaging in `stdModel_map_value_orderFlow`. (Lemma 2.1's
  second clause — the everywhere-positive density `p_Y` of `Y` — is
  already banked, as `KyleModel.map_orderFlow` together with
  `lemma21_flowDensity_pos`.)
* **The posterior** (v4 §2.2; Lane-C decision D3) — `posterior φ y`, a
  `Measure ℝ` defined as one flat `withDensity` of Lebesgue measure, with
  `isProbabilityMeasure_posterior`, the transfer lemmas
  `integral_posterior` / `integrable_posterior_iff`, and
  `inverseRegression_eq_integral_posterior` (`P(y) = ∫ v π_y(dv)`).
* **v4 Lemma 2.5, first clause** — `memLp_id_posterior`,
  `memLp_strategy_posterior`: `id, φ ∈ L²(π_y)`, from the uniform kernel
  bounds `t²ϱ(t) ≤ 2e²(2π)^{-1/2}` and
  `φ(v)²ϱ(y − φ(v)) ≤ (2y² + 4e²)(2π)^{-1/2}` (the paper's
  `(y − t)²ϱ(t) ≤ 2M²ϱ(t) + 2t²ϱ(t)`).
* **v4 eq. (2.7)** — `deriv_inverseRegression_eq_cov`:
  `P′(y) = Cov_{π_y}(id, φ)`, via the quotient rule of
  `hasDerivAt_inverseRegression` and the two score identities
  `p′(y) = −y·p_Y(y) + E_γ[φ(V)ϱ(y − φ(V))]`,
  `n′(y) = −y·n(y) + E_γ[Vφ(V)ϱ(y − φ(V))]`;
  `deriv_inverseRegression_eq_symm` is its symmetrised form, and
  `deriv_inverseRegression_pos` / `strictMono_inverseRegression` are the
  strict-positivity consequences under `StrictMono φ`.
* **Node D2, v4 eq. (2.8)** — `deriv_gaussianSmoothing_pos`,
  `strictMono_gaussianSmoothing`: `F′ > 0` from `StrictMono P` by the same
  symmetrisation, now on `γ ⊗ γ` via
  `E[(U₀ − U₁)(P(x + U₀) − P(x + U₁))] = 2F′(x)`; plus the
  `StrictMono φ`-fronted forms `deriv_gaussianSmoothing_pos_of_strictMono`
  and `strictMono_gaussianSmoothing_of_strictMono`.

The symmetrisation machinery (`integrable_symm`, `integral_symm_eq`,
`integral_symm_pos`) is stated for an arbitrary probability measure on `ℝ`
and used twice: for `π_y` and `φ` (eq. (2.7)), and for `γ` and
`u ↦ P(x + u)` (eq. (2.8)). Atomlessness of the relevant measure — the
input that makes the diagonal null — comes from
`NullSingletonClass.withDensity` for `π_y` and from
`nullSingletonClass_gaussianReal` for `γ`.

## Hypotheses added beyond the paper

Nothing mathematical. Two bookkeeping departures:

* **Lane-C decision D3**: this file does *not* import
  `KyleUniqueness.ValueFunction`, so the strict monotonicity of `φ` that
  v4 Lemma 2.4 supplies is carried as an **explicit hypothesis**
  `hmono : StrictMono φ` wherever the paper would quote Lemma 2.4. eq.
  (2.8) is additionally stated under the weaker, downstream-friendly
  hypothesis `hP : StrictMono (inverseRegression φ)`, so the two waves
  stay decoupled.
* Every statement carries `Measurable φ` — the paper's standing "Borel
  `φ`" of §2's opening, which v4 leaves implicit inside §2.
-/

open MeasureTheory ProbabilityTheory Real Filter Set

open scoped ENNReal NNReal Topology

namespace KyleUniqueness

/-! ## Elementary facts about `ϱ` in the repo's `stdNormalPDF` spelling -/

/-- `ϱ ≥ 0`. -/
lemma stdNormalPDF_nonneg (t : ℝ) : 0 ≤ stdNormalPDF t := gaussianPDFReal_nonneg 0 1 t

/-- `ϱ > 0` everywhere. -/
lemma stdNormalPDF_pos (t : ℝ) : 0 < stdNormalPDF t :=
  gaussianPDFReal_pos 0 1 t one_ne_zero

/-- `ϱ ≤ (2π)^{-1/2}` (v4 §2.2's "because `ϱ ≤ (2π)^{-1/2}`"). -/
lemma stdNormalPDF_le (t : ℝ) : stdNormalPDF t ≤ (√(2 * π))⁻¹ := by
  rw [stdNormalPDF]
  simpa using gaussianPDFReal_le 0 1 t

/-- `ϱ` is continuous (exported for the downstream nodes). -/
lemma continuous_stdNormalPDF : Continuous stdNormalPDF :=
  continuous_gaussianPDFReal 0 1

/-- `ϱ` is measurable. -/
lemma measurable_stdNormalPDF : Measurable stdNormalPDF :=
  measurable_gaussianPDFReal 0 1

/-- `|t|·ϱ(t) ≤ 2e^{1/2}(2π)^{-1/2}`, in the `stdNormalPDF` spelling. -/
lemma abs_mul_stdNormalPDF_le_const (t : ℝ) :
    |t| * stdNormalPDF t ≤ 2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹ :=
  abs_mul_gaussianPDFReal_std_le_const t

/-- Shift identity `e^{ct}ϱ(t) = e^{c²/2}ϱ(t − c)`, in the `stdNormalPDF`
spelling. -/
lemma exp_mul_stdNormalPDF (c t : ℝ) :
    Real.exp (c * t) * stdNormalPDF t = Real.exp (c ^ 2 / 2) * stdNormalPDF (t - c) :=
  exp_mul_gaussianPDFReal_std c t

/-- Second-moment kernel bound: `t²·ϱ(t) ≤ 2e²(2π)^{-1/2}`. Proof: `|t| ≤
e^{|t|}` gives `t² ≤ e^{2|t|} ≤ e^{2t} + e^{−2t}`, and the shift identity
turns each term into `e²ϱ(t ∓ 2) ≤ e²(2π)^{-1/2}`. -/
lemma sq_mul_stdNormalPDF_le_const (t : ℝ) :
    t ^ 2 * stdNormalPDF t ≤ 2 * Real.exp 2 * (√(2 * π))⁻¹ := by
  have h0 : (0:ℝ) ≤ stdNormalPDF t := stdNormalPDF_nonneg t
  have habs : |t| ≤ Real.exp |t| := by
    have := Real.add_one_le_exp |t|
    linarith
  have h1 : t ^ 2 ≤ Real.exp (2 * |t|) := by
    rw [← sq_abs t, sq, show (2 : ℝ) * |t| = |t| + |t| by ring, Real.exp_add]
    exact mul_self_le_mul_self (abs_nonneg t) habs
  have h2 : Real.exp (2 * |t|) ≤ Real.exp (2 * t) + Real.exp (-(2 * t)) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos ht, show 2 * -t = -(2 * t) by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have e1 : Real.exp (2 * t) * stdNormalPDF t = Real.exp 2 * stdNormalPDF (t - 2) := by
    have h := exp_mul_stdNormalPDF 2 t
    norm_num at h
    exact h
  have e2 : Real.exp (-(2 * t)) * stdNormalPDF t
      = Real.exp 2 * stdNormalPDF (t + 2) := by
    have h := exp_mul_stdNormalPDF (-2) t
    norm_num [sub_neg_eq_add] at h
    exact h
  calc t ^ 2 * stdNormalPDF t
      ≤ Real.exp (2 * |t|) * stdNormalPDF t := mul_le_mul_of_nonneg_right h1 h0
    _ ≤ (Real.exp (2 * t) + Real.exp (-(2 * t))) * stdNormalPDF t :=
        mul_le_mul_of_nonneg_right h2 h0
    _ = Real.exp 2 * stdNormalPDF (t - 2) + Real.exp 2 * stdNormalPDF (t + 2) := by
        rw [add_mul, e1, e2]
    _ ≤ Real.exp 2 * (√(2 * π))⁻¹ + Real.exp 2 * (√(2 * π))⁻¹ :=
        add_le_add
          (mul_le_mul_of_nonneg_left (stdNormalPDF_le _) (Real.exp_pos 2).le)
          (mul_le_mul_of_nonneg_left (stdNormalPDF_le _) (Real.exp_pos 2).le)
    _ = 2 * Real.exp 2 * (√(2 * π))⁻¹ := by ring

/-- First-moment bound in the form used for `φ ∈ L¹(π_y)`:
`|y − t|·ϱ(t) ≤ (|y| + 2e^{1/2})(2π)^{-1/2}`. -/
lemma abs_sub_mul_stdNormalPDF_le (y t : ℝ) :
    |y - t| * stdNormalPDF t ≤ (|y| + 2 * Real.exp (1/2 : ℝ)) * (√(2 * π))⁻¹ := by
  calc |y - t| * stdNormalPDF t
      ≤ (|y| + |t|) * stdNormalPDF t :=
        mul_le_mul_of_nonneg_right (abs_sub y t) (stdNormalPDF_nonneg t)
    _ = |y| * stdNormalPDF t + |t| * stdNormalPDF t := add_mul _ _ _
    _ ≤ |y| * (√(2 * π))⁻¹ + 2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left (stdNormalPDF_le t) (abs_nonneg y))
          (abs_mul_stdNormalPDF_le_const t)
    _ = (|y| + 2 * Real.exp (1/2 : ℝ)) * (√(2 * π))⁻¹ := by ring

/-- Second-moment bound in the form used for `φ ∈ L²(π_y)` (v4 Lemma 2.5's
`(y − t)²ϱ(t) ≤ 2M²ϱ(t) + 2t²ϱ(t)`):
`(y − t)²·ϱ(t) ≤ (2y² + 4e²)(2π)^{-1/2}`. -/
lemma sq_sub_mul_stdNormalPDF_le (y t : ℝ) :
    (y - t) ^ 2 * stdNormalPDF t ≤ (2 * y ^ 2 + 4 * Real.exp 2) * (√(2 * π))⁻¹ := by
  have h0 : (0:ℝ) ≤ stdNormalPDF t := stdNormalPDF_nonneg t
  calc (y - t) ^ 2 * stdNormalPDF t
      ≤ (2 * y ^ 2 + 2 * t ^ 2) * stdNormalPDF t := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        nlinarith [sq_nonneg (y + t)]
    _ = 2 * (y ^ 2 * stdNormalPDF t) + 2 * (t ^ 2 * stdNormalPDF t) := by ring
    _ ≤ 2 * (y ^ 2 * (√(2 * π))⁻¹) + 2 * (2 * Real.exp 2 * (√(2 * π))⁻¹) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (stdNormalPDF_le t) (sq_nonneg y))
            (by norm_num))
          (mul_le_mul_of_nonneg_left (sq_mul_stdNormalPDF_le_const t) (by norm_num))
    _ = (2 * y ^ 2 + 4 * Real.exp 2) * (√(2 * π))⁻¹ := by ring

/-- `|φ(v)|·ϱ(y − φ(v)) ≤ (|y| + 2e^{1/2})(2π)^{-1/2}`, uniformly in `v`. -/
lemma abs_strategy_mul_kernel_le (φ : ℝ → ℝ) (y v : ℝ) :
    |φ v| * stdNormalPDF (y - φ v)
      ≤ (|y| + 2 * Real.exp (1/2 : ℝ)) * (√(2 * π))⁻¹ := by
  have h := abs_sub_mul_stdNormalPDF_le y (y - φ v)
  rwa [show y - (y - φ v) = φ v from by ring] at h

/-- `φ(v)²·ϱ(y − φ(v)) ≤ (2y² + 4e²)(2π)^{-1/2}`, uniformly in `v` (v4
Lemma 2.5: "the right-hand side is bounded uniformly in `t`"). -/
lemma sq_strategy_mul_kernel_le (φ : ℝ → ℝ) (y v : ℝ) :
    φ v ^ 2 * stdNormalPDF (y - φ v)
      ≤ (2 * y ^ 2 + 4 * Real.exp 2) * (√(2 * π))⁻¹ := by
  have h := sq_sub_mul_stdNormalPDF_le y (y - φ v)
  rwa [show y - (y - φ v) = φ v from by ring] at h

/-! ## `ϱ`-weighted Lebesgue form of the §2 integrals -/

/-- Standard-normal expectation as a `ϱ`-weighted Lebesgue integral. -/
lemma integral_gaussianReal_std (f : ℝ → ℝ) :
    ∫ v, f v ∂(gaussianReal 0 1 : Measure ℝ) = ∫ v, stdNormalPDF v * f v := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [stdNormalPDF, smul_eq_mul]

/-- v4 Lemma 2.1, Lebesgue form of the flow density:
`p_Y(y) = ∫ ϱ(v)·ϱ(y − φ(v)) dv`. -/
lemma flowDensity_eq_integral_volume (φ : ℝ → ℝ) (y : ℝ) :
    flowDensity φ y = ∫ v, stdNormalPDF v * stdNormalPDF (y - φ v) :=
  integral_gaussianReal_std _

/-! ## Node A1b: the joint law of `(V, Y)` (v4 Lemma 2.1, first clause) -/

/-- The joint density `(v, y) ↦ ϱ(v)·ϱ(y − φ(v))` of v4 Lemma 2.1, as an
`ℝ≥0∞`-valued function on `ℝ × ℝ`. -/
noncomputable def jointDensity (φ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (stdNormalPDF p.1 * stdNormalPDF (p.2 - φ p.1))

lemma measurable_jointDensity {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (jointDensity φ) :=
  ((((measurable_gaussianPDFReal 0 1).comp measurable_fst).mul
    ((measurable_gaussianPDFReal 0 1).comp
      (measurable_snd.sub (hφ.comp measurable_fst))))).ennreal_ofReal

/-- **v4 Lemma 2.1, joint-density clause** (blueprint node A1b): on the
normalised model the joint law of `(V, Y) = (V, φ(V) + U)` — the pushforward
of `γ ⊗ γ` under the shear `(v, u) ↦ (v, φ(v) + u)` — is two-dimensional
Lebesgue measure weighted by `ϱ(v)·ϱ(y − φ(v))`. -/
theorem map_value_orderFlow {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => (p.1, φ p.1 + p.2))
      = (volume : Measure (ℝ × ℝ)).withDensity (jointDensity φ) := by
  have hT : Measurable fun p : ℝ × ℝ => (p.1, φ p.1 + p.2) :=
    measurable_fst.prodMk ((hφ.comp measurable_fst).add measurable_snd)
  have hd := measurable_jointDensity hφ
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hT hs, Measure.prod_apply (hT hs), withDensity_apply _ hs]
  -- the inner slice: translate the noise integral to a `ϱ`-weighted Lebesgue one
  have hslice : ∀ v : ℝ,
      (gaussianReal 0 1 : Measure ℝ)
          (Prod.mk v ⁻¹' ((fun p : ℝ × ℝ => (p.1, φ p.1 + p.2)) ⁻¹' s))
        = ∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - φ v))
            * s.indicator 1 (v, y) ∂(volume : Measure ℝ) := by
    intro v
    have hA : MeasurableSet (Prod.mk v ⁻¹' s) := measurable_prodMk_left hs
    have hpre : Prod.mk v ⁻¹' ((fun p : ℝ × ℝ => (p.1, φ p.1 + p.2)) ⁻¹' s)
        = (fun u => φ v + u) ⁻¹' (Prod.mk v ⁻¹' s) := rfl
    have hind : ∀ u : ℝ,
        ((fun u => φ v + u) ⁻¹' (Prod.mk v ⁻¹' s)).indicator (1 : ℝ → ℝ≥0∞) u
          = (Prod.mk v ⁻¹' s).indicator 1 (φ v + u) := by
      intro u
      by_cases h : φ v + u ∈ Prod.mk v ⁻¹' s
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by exact h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]
    rw [hpre, ← lintegral_indicator_one (measurable_const_add (φ v) hA),
      lintegral_congr hind,
      lintegral_comp_add_gaussianReal' one_ne_zero (φ v)
        (measurable_one.indicator hA)]
    rfl
  -- the outer integral: unfold the Gaussian prior as a `withDensity`
  have houter : ∫⁻ v, (gaussianReal 0 1 : Measure ℝ)
        (Prod.mk v ⁻¹' ((fun p : ℝ × ℝ => (p.1, φ p.1 + p.2)) ⁻¹' s))
        ∂gaussianReal 0 1
      = ∫⁻ v, ENNReal.ofReal (stdNormalPDF v)
          * ∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - φ v))
            * s.indicator 1 (v, y) ∂(volume : Measure ℝ) ∂(volume : Measure ℝ) := by
    have hinner : Measurable fun v : ℝ =>
        ∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - φ v))
          * s.indicator 1 (v, y) ∂(volume : Measure ℝ) := by
      refine Measurable.lintegral_prod_right ?_
      exact (((measurable_gaussianPDFReal 0 1).comp
        (measurable_snd.sub (hφ.comp measurable_fst))).ennreal_ofReal).mul
          ((measurable_one.indicator hs).comp
            (measurable_fst.prodMk measurable_snd))
    rw [lintegral_congr hslice, gaussianReal_of_var_ne_zero _ one_ne_zero,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hinner]
    rfl
  rw [houter, ← lintegral_indicator hs, Measure.volume_eq_prod ℝ ℝ,
    lintegral_prod _ (hd.indicator hs).aemeasurable]
  refine lintegral_congr fun v => ?_
  have hmeas : Measurable fun y : ℝ =>
      ENNReal.ofReal (stdNormalPDF (y - φ v)) * s.indicator 1 (v, y) := by
    refine Measurable.mul ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 1).comp
        (measurable_id.sub_const (φ v))).ennreal_ofReal
    · exact (measurable_one.indicator hs).comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_const_mul _ hmeas]
  refine lintegral_congr fun y => ?_
  by_cases h : (v, y) ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul (stdNormalPDF_nonneg v)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, mul_zero]

/-- Node A1b in `stdModel` packaging: the law of the pair `(V, Y_φ)` under
the normalised model of v4 §2. -/
theorem stdModel_map_value_orderFlow {φ : ℝ → ℝ} (hφ : Measurable φ) :
    stdModel.μ.map (fun ω => (stdModel.V ω, stdModel.orderFlow φ ω))
      = (volume : Measure (ℝ × ℝ)).withDensity (jointDensity φ) :=
  map_value_orderFlow hφ

/-! ## The posterior `π_y` (v4 §2.2, node D3) -/

/-- The posterior density `v ↦ ϱ(v)·ϱ(y − φ(v))/p_Y(y)` of v4 §2.2. -/
noncomputable def posteriorDensity (φ : ℝ → ℝ) (y v : ℝ) : ℝ :=
  stdNormalPDF v * stdNormalPDF (y - φ v) / flowDensity φ y

/-- **The posterior `π_y`** (v4 §2.2):
`π_y(dv) = ϱ(v)·ϱ(y − φ(v))/p_Y(y) dv`, the version of the conditional law
of `V` given `Y = y` supplied by v4 Lemma 2.1 and Bayes' formula. -/
noncomputable def posterior (φ : ℝ → ℝ) (y : ℝ) : Measure ℝ :=
  volume.withDensity fun v => ENNReal.ofReal (posteriorDensity φ y v)

lemma posteriorDensity_pos {φ : ℝ → ℝ} (hφ : Measurable φ) (y v : ℝ) :
    0 < posteriorDensity φ y v :=
  div_pos (mul_pos (stdNormalPDF_pos _) (stdNormalPDF_pos _))
    (lemma21_flowDensity_pos hφ y)

lemma posteriorDensity_nonneg {φ : ℝ → ℝ} (hφ : Measurable φ) (y v : ℝ) :
    0 ≤ posteriorDensity φ y v := (posteriorDensity_pos hφ y v).le

lemma measurable_posteriorDensity {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Measurable (posteriorDensity φ y) :=
  (measurable_stdNormalPDF.mul
    (measurable_stdNormalPDF.comp (measurable_const.sub hφ))).div_const _

/-! ### Integrability of the Bayes kernels -/

/-- The noise kernel `v ↦ ϱ(y − φ(v))` is `γ`-integrable (it is bounded). -/
lemma integrable_kernel_gaussian {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => stdNormalPDF (y - φ v)) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const ((√(2 * π))⁻¹))
    (measurable_stdNormalPDF.comp (measurable_const.sub hφ)).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (stdNormalPDF_nonneg _)]
  exact stdNormalPDF_le _

/-- The joint kernel `v ↦ ϱ(v)·ϱ(y − φ(v))` is Lebesgue-integrable. -/
lemma integrable_kernel_volume {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => stdNormalPDF v * stdNormalPDF (y - φ v))
      (volume : Measure ℝ) :=
  (integrable_gaussianReal_iff one_ne_zero).mp (integrable_kernel_gaussian hφ y)

/-- The posterior density is Lebesgue-integrable. -/
lemma integrable_posteriorDensity {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (posteriorDensity φ y) (volume : Measure ℝ) :=
  (integrable_kernel_volume hφ y).div_const _

/-- The posterior density integrates to one (v4 Lemma 2.1: `p_Y(y) > 0` is
exactly what makes the normalisation legitimate). -/
lemma integral_posteriorDensity {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    ∫ v, posteriorDensity φ y v = 1 := by
  simp only [posteriorDensity]
  rw [integral_div, ← flowDensity_eq_integral_volume,
    div_self (lemma21_flowDensity_pos hφ y).ne']

/-- **`π_y` is a probability measure** (v4 §2.2). -/
theorem isProbabilityMeasure_posterior {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) : IsProbabilityMeasure (posterior φ y) := by
  constructor
  rw [posterior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_posteriorDensity hφ y)
      (ae_of_all _ fun v => posteriorDensity_nonneg hφ y v),
    integral_posteriorDensity hφ y, ENNReal.ofReal_one]

/-- `π_y` is atomless (its density is Lebesgue): the glue that makes the
diagonal `(π_y ⊗ π_y)`-null in the symmetrised covariance. -/
instance nullSingletonClass_posterior (φ : ℝ → ℝ) (y : ℝ) :
    NullSingletonClass (posterior φ y) :=
  NullSingletonClass.withDensity _

/-! ### Transfer between `π_y`-integrals and the Bayes quotient -/

/-- Bochner integrals against `π_y` are Bayes quotients: for every `g`,
`∫ g dπ_y = (∫ g(v)ϱ(y − φ(v)) γ(dv))/p_Y(y)`. (No hypothesis on `g`: both
sides are `0` when `g` is not integrable.) -/
theorem integral_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ)
    (g : ℝ → ℝ) :
    ∫ v, g v ∂posterior φ y
      = (∫ v, g v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1)
        / flowDensity φ y := by
  rw [posterior, integral_withDensity_eq_integral_toReal_smul
    (measurable_posteriorDensity hφ y).ennreal_ofReal
    (ae_of_all _ fun v => ENNReal.ofReal_lt_top),
    integral_gaussianReal_std, ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  beta_reduce
  rw [smul_eq_mul, ENNReal.toReal_ofReal (posteriorDensity_nonneg hφ y v),
    posteriorDensity]
  ring

/-- Integrability against `π_y` is integrability of the weighted kernel. -/
theorem integrable_posterior_iff {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ)
    {g : ℝ → ℝ} :
    Integrable g (posterior φ y)
      ↔ Integrable (fun v => posteriorDensity φ y v * g v)
          (volume : Measure ℝ) := by
  rw [posterior, integrable_withDensity_iff_integrable_smul'
    (measurable_posteriorDensity hφ y).ennreal_ofReal
    (ae_of_all _ fun v => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun v => ?_)
  beta_reduce
  rw [smul_eq_mul, ENNReal.toReal_ofReal (posteriorDensity_nonneg hφ y v)]

/-- **v4 §2.2, last display**: `P(y) = ∫ v π_y(dv)` — the inverse regression
is the posterior mean. -/
theorem inverseRegression_eq_integral_posterior {φ : ℝ → ℝ}
    (hφ : Measurable φ) (y : ℝ) :
    inverseRegression φ y = ∫ v, v ∂posterior φ y :=
  (integral_posterior hφ y fun v => v).symm

/-! ## v4 Lemma 2.5, first clause: `id, φ ∈ L²(π_y)` -/

/-- The Gaussian has a second moment. -/
lemma integrable_sq_gaussianReal_std :
    Integrable (fun v : ℝ => v ^ 2) (gaussianReal 0 1) := by
  have hmem : MemLp id 2 (gaussianReal (0 : ℝ) 1) := by
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp hmem

/-- `v ↦ ϱ(v)·v²` is Lebesgue-integrable. -/
lemma integrable_sq_mul_stdNormalPDF :
    Integrable (fun v => stdNormalPDF v * v ^ 2) (volume : Measure ℝ) :=
  (integrable_gaussianReal_iff one_ne_zero).mp integrable_sq_gaussianReal_std

/-- `ϱ` is Lebesgue-integrable. -/
lemma integrable_stdNormalPDF :
    Integrable stdNormalPDF (volume : Measure ℝ) :=
  integrable_gaussianPDFReal 0 1

/-- v4 Lemma 2.5: `∫ v²ϱ(v)ϱ(y − φ(v)) dv ≤ (2π)^{-1/2}·∫ v²ϱ(v) dv < ∞`. -/
lemma integrable_sq_kernel_volume {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => stdNormalPDF v * stdNormalPDF (y - φ v) * v ^ 2)
      (volume : Measure ℝ) := by
  refine Integrable.mono'
    (integrable_sq_mul_stdNormalPDF.const_mul ((√(2 * π))⁻¹))
    (((measurable_stdNormalPDF.mul (measurable_stdNormalPDF.comp
      (measurable_const.sub hφ))).mul
        (measurable_id.pow_const 2)).aestronglyMeasurable)
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (stdNormalPDF_nonneg _)
    (stdNormalPDF_nonneg _)) (sq_nonneg v))]
  calc stdNormalPDF v * stdNormalPDF (y - φ v) * v ^ 2
      = (stdNormalPDF v * v ^ 2) * stdNormalPDF (y - φ v) := by ring
    _ ≤ (stdNormalPDF v * v ^ 2) * (√(2 * π))⁻¹ :=
        mul_le_mul_of_nonneg_left (stdNormalPDF_le _)
          (mul_nonneg (stdNormalPDF_nonneg v) (sq_nonneg v))
    _ = (√(2 * π))⁻¹ * (stdNormalPDF v * v ^ 2) := by ring

/-- v4 Lemma 2.5: `φ(v)²ϱ(y − φ(v))` is uniformly bounded, so
`∫ φ(v)²ϱ(v)ϱ(y − φ(v)) dv < ∞`. -/
lemma integrable_sq_strategy_kernel_volume {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    Integrable (fun v => stdNormalPDF v * stdNormalPDF (y - φ v) * φ v ^ 2)
      (volume : Measure ℝ) := by
  refine Integrable.mono'
    (integrable_stdNormalPDF.const_mul
      ((2 * y ^ 2 + 4 * Real.exp 2) * (√(2 * π))⁻¹))
    (((measurable_stdNormalPDF.mul (measurable_stdNormalPDF.comp
      (measurable_const.sub hφ))).mul (hφ.pow_const 2)).aestronglyMeasurable)
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (stdNormalPDF_nonneg _)
    (stdNormalPDF_nonneg _)) (sq_nonneg (φ v)))]
  calc stdNormalPDF v * stdNormalPDF (y - φ v) * φ v ^ 2
      = stdNormalPDF v * (φ v ^ 2 * stdNormalPDF (y - φ v)) := by ring
    _ ≤ stdNormalPDF v * ((2 * y ^ 2 + 4 * Real.exp 2) * (√(2 * π))⁻¹) :=
        mul_le_mul_of_nonneg_left (sq_strategy_mul_kernel_le φ y v)
          (stdNormalPDF_nonneg v)
    _ = (2 * y ^ 2 + 4 * Real.exp 2) * (√(2 * π))⁻¹ * stdNormalPDF v := by ring

/-- **v4 Lemma 2.5, first clause (`id`)**: the identity is in `L²(π_y)`. -/
theorem memLp_id_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    MemLp id 2 (posterior φ y) := by
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr ?_
  rw [integrable_posterior_iff hφ y]
  refine ((integrable_sq_kernel_volume hφ y).const_mul
    (flowDensity φ y)⁻¹).congr (ae_of_all _ fun v => ?_)
  simp only [posteriorDensity, id_eq]
  ring

/-- **v4 Lemma 2.5, first clause (`φ`)**: the strategy is in `L²(π_y)`. -/
theorem memLp_strategy_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    MemLp φ 2 (posterior φ y) := by
  refine (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mpr ?_
  rw [integrable_posterior_iff hφ y]
  refine ((integrable_sq_strategy_kernel_volume hφ y).const_mul
    (flowDensity φ y)⁻¹).congr (ae_of_all _ fun v => ?_)
  simp only [posteriorDensity]
  ring

/-! ## v4 Lemma 2.5, eq. (2.7): `P′(y) = Cov_{π_y}(id, φ)`

The route is the quotient rule of `hasDerivAt_inverseRegression` plus the
two kernel identities `n′(y) = −y·n(y) + E_γ[Vφ(V)ϱ(y − φ(V))]` and
`p′(y) = −y·p(y) + E_γ[φ(V)ϱ(y − φ(V))]`, after which the algebra collapses
to the covariance. -/

/-- Domination helper: a measurable function with a constant bound is
`γ`-integrable. -/
private lemma integrable_of_bound_const {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ v, ‖f v‖ ≤ C) : Integrable f (gaussianReal 0 1) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (ae_of_all _ hC)

/-- Domination helper: a measurable function bounded by `C·|v|` is
`γ`-integrable. -/
private lemma integrable_of_bound_abs {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ v, ‖f v‖ ≤ C * |v|) : Integrable f (gaussianReal 0 1) :=
  Integrable.mono' (((integrable_id_gaussianReal 0 1).abs).const_mul C)
    hf.aestronglyMeasurable (ae_of_all _ hC)

/-- `v ↦ v·ϱ(y − φ(v))` is `γ`-integrable (the Bayes numerator kernel). -/
lemma integrable_numerator_kernel {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => v * stdNormalPDF (y - φ v)) (gaussianReal 0 1) := by
  refine integrable_of_bound_abs
    (measurable_id.mul (measurable_stdNormalPDF.comp
      (measurable_const.sub hφ))) (C := (√(2 * π))⁻¹) fun v => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg _)]
  calc |v| * stdNormalPDF (y - φ v) ≤ |v| * (√(2 * π))⁻¹ :=
        mul_le_mul_of_nonneg_left (stdNormalPDF_le _) (abs_nonneg v)
    _ = (√(2 * π))⁻¹ * |v| := mul_comm _ _

/-- `v ↦ φ(v)·ϱ(y − φ(v))` is `γ`-integrable (it is uniformly bounded). -/
lemma integrable_strategy_kernel {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => φ v * stdNormalPDF (y - φ v)) (gaussianReal 0 1) := by
  refine integrable_of_bound_const
    (hφ.mul (measurable_stdNormalPDF.comp (measurable_const.sub hφ)))
    (C := (|y| + 2 * Real.exp (1/2 : ℝ)) * (√(2 * π))⁻¹) fun v => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg _)]
  exact abs_strategy_mul_kernel_le φ y v

/-- `v ↦ v·φ(v)·ϱ(y − φ(v))` is `γ`-integrable. -/
lemma integrable_mixed_kernel {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => v * φ v * stdNormalPDF (y - φ v))
      (gaussianReal 0 1) := by
  refine integrable_of_bound_abs
    ((measurable_id.mul hφ).mul (measurable_stdNormalPDF.comp
      (measurable_const.sub hφ)))
    (C := (|y| + 2 * Real.exp (1/2 : ℝ)) * (√(2 * π))⁻¹) fun v => ?_
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_mul,
    abs_of_nonneg (stdNormalPDF_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_strategy_mul_kernel_le φ y v)
    (abs_nonneg v)

/-- `v ↦ (y − φ(v))·ϱ(y − φ(v))` is `γ`-integrable — the integrand of
`−p′(y)` (`hasDerivAt_flowDensity`); exported for the downstream nodes. -/
lemma integrable_score_kernel {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => (y - φ v) * stdNormalPDF (y - φ v))
      (gaussianReal 0 1) := by
  refine integrable_of_bound_const
    ((measurable_const.sub hφ).mul (measurable_stdNormalPDF.comp
      (measurable_const.sub hφ)))
    (C := 2 * Real.exp (1/2 : ℝ) * (√(2 * π))⁻¹) fun v => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg _)]
  exact abs_mul_stdNormalPDF_le_const (y - φ v)

/-- v4 Lemma 2.5: `p′(y) = −y·p_Y(y) + E_γ[φ(V)ϱ(y − φ(V))]`. -/
lemma integral_flowDensity_deriv_kernel {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    (∫ v, -((y - φ v) * stdNormalPDF (y - φ v)) ∂gaussianReal 0 1)
      = -(y * flowDensity φ y)
        + ∫ v, φ v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1 := by
  have hker := integrable_kernel_gaussian hφ y
  have hL := integrable_strategy_kernel hφ y
  have e : (fun v => -((y - φ v) * stdNormalPDF (y - φ v)))
      = fun v => -(y * stdNormalPDF (y - φ v))
        + φ v * stdNormalPDF (y - φ v) := funext fun v => by ring
  have h1 : Integrable (fun v => -(y * stdNormalPDF (y - φ v)))
      (gaussianReal 0 1) := (hker.const_mul y).neg
  rw [e, integral_add h1 hL, integral_neg, integral_const_mul]
  rfl

/-- v4 Lemma 2.5: `n′(y) = −y·n(y) + E_γ[Vφ(V)ϱ(y − φ(V))]`. -/
lemma integral_flowNumerator_deriv_kernel {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    (∫ v, -(v * ((y - φ v) * stdNormalPDF (y - φ v))) ∂gaussianReal 0 1)
      = -(y * ∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1)
        + ∫ v, v * φ v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1 := by
  have hn := integrable_numerator_kernel hφ y
  have hM := integrable_mixed_kernel hφ y
  have e : (fun v => -(v * ((y - φ v) * stdNormalPDF (y - φ v))))
      = fun v => -(y * (v * stdNormalPDF (y - φ v)))
        + v * φ v * stdNormalPDF (y - φ v) := funext fun v => by ring
  have h1 : Integrable (fun v => -(y * (v * stdNormalPDF (y - φ v))))
      (gaussianReal 0 1) := (hn.const_mul y).neg
  rw [e, integral_add h1 hM, integral_neg, integral_const_mul]

/-- **v4 Lemma 2.5, eq. (2.7)** (blueprint node D1): the derivative of the
inverse regression is the posterior covariance of the identity and the
strategy,
`P′(y) = E_{π_y}[id·φ] − E_{π_y}[id]·E_{π_y}[φ] = Cov_{π_y}(id, φ)`. -/
theorem deriv_inverseRegression_eq_cov {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    deriv (inverseRegression φ) y
      = (∫ v, v * φ v ∂posterior φ y)
        - (∫ v, v ∂posterior φ y) * ∫ v, φ v ∂posterior φ y := by
  have hp0 : flowDensity φ y ≠ 0 := (lemma21_flowDensity_pos hφ y).ne'
  rw [(hasDerivAt_inverseRegression hφ y).deriv,
    integral_flowNumerator_deriv_kernel hφ y,
    integral_flowDensity_deriv_kernel hφ y,
    integral_posterior hφ y fun v => v * φ v,
    integral_posterior hφ y fun v => v,
    integral_posterior hφ y φ]
  field_simp
  ring

/-! ## The symmetrisation identity on a product of probability measures

`∫∫ (v − w)(g(v) − g(w)) μ(dv) μ(dw) = 2·Cov_μ(id, g)` — the identity v4
Lemma 2.5 uses twice, once for `π_y` and `φ` (eq. (2.7)) and once for `γ`
and `u ↦ P(x + u)` (eq. (2.8)). -/

/-- Product-integrability of the symmetrised integrand. -/
theorem integrable_symm {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hid : Integrable (fun v : ℝ => v) μ) (hg : Integrable g μ)
    (hmul : Integrable (fun v => v * g v) μ) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) * (g p.1 - g p.2))
      (μ.prod μ) := by
  have j1 : Integrable (fun p : ℝ × ℝ => p.1 * g p.1) (μ.prod μ) := by
    simpa using hmul.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have j2 : Integrable (fun p : ℝ × ℝ => p.1 * g p.2) (μ.prod μ) :=
    hid.mul_prod hg
  have j3 : Integrable (fun p : ℝ × ℝ => g p.1 * p.2) (μ.prod μ) :=
    hg.mul_prod hid
  have j4 : Integrable (fun p : ℝ × ℝ => p.2 * g p.2) (μ.prod μ) := by
    simpa using (integrable_const (1 : ℝ) (μ := μ)).mul_prod hmul
  have k : Integrable
      (fun p : ℝ × ℝ => (p.1 * g p.1 - p.1 * g p.2)
        + (p.2 * g p.2 - g p.1 * p.2)) (μ.prod μ) := (j1.sub j2).add (j4.sub j3)
  exact k.congr (ae_of_all _ fun p => by ring)

/-- **Symmetrisation**: `∫∫ (v − w)(g(v) − g(w)) = 2·Cov_μ(id, g)`. -/
theorem integral_symm_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} (hid : Integrable (fun v : ℝ => v) μ) (hg : Integrable g μ)
    (hmul : Integrable (fun v => v * g v) μ) :
    ∫ p, (p.1 - p.2) * (g p.1 - g p.2) ∂(μ.prod μ)
      = 2 * ((∫ v, v * g v ∂μ) - (∫ v, v ∂μ) * ∫ v, g v ∂μ) := by
  have j1 : Integrable (fun p : ℝ × ℝ => p.1 * g p.1) (μ.prod μ) := by
    simpa using hmul.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have j2 : Integrable (fun p : ℝ × ℝ => p.1 * g p.2) (μ.prod μ) :=
    hid.mul_prod hg
  have j3 : Integrable (fun p : ℝ × ℝ => g p.1 * p.2) (μ.prod μ) :=
    hg.mul_prod hid
  have j4 : Integrable (fun p : ℝ × ℝ => p.2 * g p.2) (μ.prod μ) := by
    simpa using (integrable_const (1 : ℝ) (μ := μ)).mul_prod hmul
  have i1 : ∫ p : ℝ × ℝ, p.1 * g p.1 ∂(μ.prod μ) = ∫ v, v * g v ∂μ := by
    simpa using integral_prod_mul (μ := μ) (ν := μ) (fun v => v * g v)
      (fun _ => (1 : ℝ))
  have i2 : ∫ p : ℝ × ℝ, p.1 * g p.2 ∂(μ.prod μ)
      = (∫ v, v ∂μ) * ∫ v, g v ∂μ := integral_prod_mul (fun v => v) g
  have i3 : ∫ p : ℝ × ℝ, g p.1 * p.2 ∂(μ.prod μ)
      = (∫ v, g v ∂μ) * ∫ v, v ∂μ := integral_prod_mul g (fun w => w)
  have i4 : ∫ p : ℝ × ℝ, p.2 * g p.2 ∂(μ.prod μ) = ∫ v, v * g v ∂μ := by
    simpa using integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ))
      (fun w => w * g w)
  have hexp : ∫ p, (p.1 - p.2) * (g p.1 - g p.2) ∂(μ.prod μ)
      = ∫ p : ℝ × ℝ, ((p.1 * g p.1 - p.1 * g p.2)
          + (p.2 * g p.2 - g p.1 * p.2)) ∂(μ.prod μ) :=
    integral_congr_ae (ae_of_all _ fun p => by ring)
  have k1 : Integrable (fun p : ℝ × ℝ => p.1 * g p.1 - p.1 * g p.2)
      (μ.prod μ) := j1.sub j2
  have k2 : Integrable (fun p : ℝ × ℝ => p.2 * g p.2 - g p.1 * p.2)
      (μ.prod μ) := j4.sub j3
  rw [hexp, integral_add k1 k2, integral_sub j1 j2, integral_sub j4 j3,
    i1, i2, i3, i4]
  ring

/-! ## v4 Lemma 2.5: the symmetrised covariance for `π_y` -/

/-- `id ∈ L¹(π_y)`. -/
lemma integrable_id_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v : ℝ => v) (posterior φ y) :=
  haveI := isProbabilityMeasure_posterior hφ y
  (memLp_id_posterior hφ y).integrable one_le_two

/-- `φ ∈ L¹(π_y)`. -/
lemma integrable_strategy_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable φ (posterior φ y) :=
  haveI := isProbabilityMeasure_posterior hφ y
  (memLp_strategy_posterior hφ y).integrable one_le_two

/-- `id·φ ∈ L¹(π_y)` (Cauchy–Schwarz from the two `L²` clauses of v4
Lemma 2.5). -/
lemma integrable_mul_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => v * φ v) (posterior φ y) :=
  (memLp_id_posterior hφ y).integrable_mul (memLp_strategy_posterior hφ y)

/-- The symmetrised integrand is `π_y ⊗ π_y`-integrable. -/
lemma integrable_symm_posterior {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) * (φ p.1 - φ p.2))
      ((posterior φ y).prod (posterior φ y)) :=
  haveI := isProbabilityMeasure_posterior hφ y
  integrable_symm (integrable_id_posterior hφ y)
    (integrable_strategy_posterior hφ y) (integrable_mul_posterior hφ y)

/-- **v4 Lemma 2.5, symmetrised form of eq. (2.7)**:
`P′(y) = ½ ∫∫ (v − w)(φ(v) − φ(w)) π_y(dv) π_y(dw)`. -/
theorem deriv_inverseRegression_eq_symm {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    deriv (inverseRegression φ) y
      = (1/2) * ∫ p, (p.1 - p.2) * (φ p.1 - φ p.2)
          ∂((posterior φ y).prod (posterior φ y)) := by
  haveI := isProbabilityMeasure_posterior hφ y
  rw [deriv_inverseRegression_eq_cov hφ y,
    integral_symm_eq (integrable_id_posterior hφ y)
      (integrable_strategy_posterior hφ y) (integrable_mul_posterior hφ y)]
  ring

/-! ## v4 Lemma 2.5, eq. (2.7): strict positivity and `StrictMono P` -/

/-- The symmetrised integrand of a monotone map is nonnegative. -/
lemma symm_integrand_nonneg {g : ℝ → ℝ} (hg : Monotone g) (p : ℝ × ℝ) :
    0 ≤ (p.1 - p.2) * (g p.1 - g p.2) := by
  rcases le_total p.1 p.2 with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hg h])
  · exact mul_nonneg (by linarith) (by linarith [hg h])

/-- The support of the symmetrised integrand of a strictly monotone map is
exactly the complement of the diagonal. -/
lemma support_symm_eq_compl_diagonal {g : ℝ → ℝ} (hg : StrictMono g) :
    (Function.support fun p : ℝ × ℝ => (p.1 - p.2) * (g p.1 - g p.2))
      = (Set.diagonal ℝ)ᶜ := by
  ext p
  simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_diagonal_iff]
  constructor
  · intro h hdiag
    exact h (by rw [hdiag]; ring)
  · intro h
    exact mul_ne_zero (sub_ne_zero.mpr h) (sub_ne_zero.mpr (hg.injective.ne h))

/-- **The symmetrisation argument of v4 Lemma 2.5**: for a strictly
monotone `g` and an atomless probability measure `μ`, the symmetrised
integral is strictly positive — the integrand is nonnegative everywhere,
strictly positive off the diagonal, and the diagonal is `(μ ⊗ μ)`-null. -/
theorem integral_symm_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {g : ℝ → ℝ} (hg : StrictMono g)
    (hint : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) * (g p.1 - g p.2))
      (μ.prod μ)) :
    0 < ∫ p, (p.1 - p.2) * (g p.1 - g p.2) ∂(μ.prod μ) := by
  rw [integral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (symm_integrand_nonneg hg.monotone)) hint,
    support_symm_eq_compl_diagonal hg,
    measure_compl isClosed_diagonal.measurableSet (measure_ne_top _ _),
    measure_prod_diagonal_eq_zero, measure_univ, tsub_zero]
  exact zero_lt_one

/-- **v4 Lemma 2.5, eq. (2.7), strict inequality**: under the strict
monotonicity of `φ` supplied by v4 Lemma 2.4, the posterior covariance is
strictly positive, so `P′(y) > 0` for every `y`. -/
theorem deriv_inverseRegression_pos {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hmono : StrictMono φ) (y : ℝ) : 0 < deriv (inverseRegression φ) y := by
  haveI := isProbabilityMeasure_posterior hφ y
  have hpos := integral_symm_pos (μ := posterior φ y) hmono
    (integrable_symm_posterior hφ y)
  rw [deriv_inverseRegression_eq_symm hφ y]
  linarith

/-- **v4 Lemma 2.5**: the inverse regression is strictly increasing. -/
theorem strictMono_inverseRegression {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hmono : StrictMono φ) : StrictMono (inverseRegression φ) :=
  strictMono_of_deriv_pos (deriv_inverseRegression_pos hφ hmono)

/-! ## v4 Lemma 2.5, eq. (2.8): `F′ > 0` (blueprint node D2)

`F′(x) = E[U·P(x + U)]` (v4 eq. (2.3)); symmetrising on `γ ⊗ γ` gives
`E[(U₀ − U₁)(P(x + U₀) − P(x + U₁))] = 2F′(x)` because `E[U] = 0` and the
two coordinates are independent, and the symmetrised integrand is positive
off the `γ ⊗ γ`-null diagonal once `P` is strictly increasing. -/

/-- `u ↦ P(x + u)` is `γ`-integrable (the absolute convergence of v4
Lemma 2.3, banked as `lemma23_integrable`, translated by `x`). -/
lemma integrable_inverseRegression_comp_add {φ : ℝ → ℝ} (hφ : Measurable φ)
    (x : ℝ) :
    Integrable (fun u => inverseRegression φ (x + u)) (gaussianReal 0 1) := by
  refine (integrable_gaussianReal_iff one_ne_zero).mpr ?_
  refine ((lemma23_integrable hφ x).comp_add_left x).congr
    (ae_of_all _ fun u => ?_)
  beta_reduce
  rw [show x + u - x = u from by ring, stdNormalPDF]
  ring

/-- `u ↦ u·P(x + u)` is `γ`-integrable (the eq.-(2.3) derivative kernel,
translated by `x`). -/
lemma integrable_id_mul_inverseRegression_comp_add {φ : ℝ → ℝ}
    (hφ : Measurable φ) (x : ℝ) :
    Integrable (fun u => u * inverseRegression φ (x + u))
      (gaussianReal 0 1) := by
  refine (integrable_gaussianReal_iff one_ne_zero).mpr ?_
  refine ((integrable_gaussianSmoothing_deriv_kernel hφ x).comp_add_left
    x).congr (ae_of_all _ fun u => ?_)
  beta_reduce
  rw [show x + u - x = u from by ring, stdNormalPDF]
  ring

/-- `F′(x) = E[U·P(x + U)]` (v4 eq. (2.3), second form, in `deriv`
packaging). -/
lemma deriv_gaussianSmoothing_prob {φ : ℝ → ℝ} (hφ : Measurable φ) (x : ℝ) :
    deriv (gaussianSmoothing φ) x
      = ∫ u, u * inverseRegression φ (x + u) ∂gaussianReal 0 1 := by
  rw [deriv_gaussianSmoothing hφ x, deriv_gaussianSmoothing_eq_prob φ x]

/-- The translated inverse regression `u ↦ P(x + u)` inherits strict
monotonicity. -/
lemma strictMono_inverseRegression_comp_add {φ : ℝ → ℝ}
    (hP : StrictMono (inverseRegression φ)) (x : ℝ) :
    StrictMono fun u => inverseRegression φ (x + u) :=
  fun _ _ hab => hP (by linarith)

/-- **v4 Lemma 2.5, symmetrisation of eq. (2.3)**:
`E[(U₀ − U₁)(P(x + U₀) − P(x + U₁))] = 2F′(x)`. -/
theorem integral_symm_gaussianSmoothing {φ : ℝ → ℝ} (hφ : Measurable φ)
    (x : ℝ) :
    ∫ p, (p.1 - p.2) * (inverseRegression φ (x + p.1)
          - inverseRegression φ (x + p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = 2 * deriv (gaussianSmoothing φ) x := by
  have hid : Integrable (fun u : ℝ => u) (gaussianReal 0 1) :=
    integrable_id_gaussianReal 0 1
  rw [integral_symm_eq hid (integrable_inverseRegression_comp_add hφ x)
      (integrable_id_mul_inverseRegression_comp_add hφ x),
    integral_id_gaussianReal, deriv_gaussianSmoothing_prob hφ x]
  ring

/-- **v4 Lemma 2.5, eq. (2.8)** (blueprint node D2): if the inverse
regression is strictly increasing, then `F′(x) > 0` for every `x`. -/
theorem deriv_gaussianSmoothing_pos {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hP : StrictMono (inverseRegression φ)) (x : ℝ) :
    0 < deriv (gaussianSmoothing φ) x := by
  have hid : Integrable (fun u : ℝ => u) (gaussianReal 0 1) :=
    integrable_id_gaussianReal 0 1
  have hint := integrable_symm (μ := gaussianReal 0 1) hid
    (integrable_inverseRegression_comp_add hφ x)
    (integrable_id_mul_inverseRegression_comp_add hφ x)
  have hpos := integral_symm_pos (μ := gaussianReal 0 1)
    (strictMono_inverseRegression_comp_add hP x) hint
  rw [integral_symm_gaussianSmoothing hφ x] at hpos
  linarith

/-- **v4 Lemma 2.5, last clause**: the Gaussian smoothing `F` is strictly
increasing. -/
theorem strictMono_gaussianSmoothing {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hP : StrictMono (inverseRegression φ)) :
    StrictMono (gaussianSmoothing φ) :=
  strictMono_of_deriv_pos (deriv_gaussianSmoothing_pos hφ hP)

/-! ## v4 Lemma 2.5 packaged under the hypothesis of v4 Lemma 2.4

Lemma 2.4 delivers `StrictMono φ`; these are the forms the value-function
wave consumes. -/

/-- eq. (2.8) directly from the strict monotonicity of `φ`. -/
theorem deriv_gaussianSmoothing_pos_of_strictMono {φ : ℝ → ℝ}
    (hφ : Measurable φ) (hmono : StrictMono φ) (x : ℝ) :
    0 < deriv (gaussianSmoothing φ) x :=
  deriv_gaussianSmoothing_pos hφ (strictMono_inverseRegression hφ hmono) x

/-- `F` strictly increasing, directly from the strict monotonicity of
`φ`. -/
theorem strictMono_gaussianSmoothing_of_strictMono {φ : ℝ → ℝ}
    (hφ : Measurable φ) (hmono : StrictMono φ) :
    StrictMono (gaussianSmoothing φ) :=
  strictMono_gaussianSmoothing hφ (strictMono_inverseRegression hφ hmono)

end KyleUniqueness
