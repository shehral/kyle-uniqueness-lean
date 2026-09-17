/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Definitions
import KyleUniqueness.CondExpBridge
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The one-period Gaussian Kyle model has exactly one equilibrium: statements

Formal statements of the theorems of Monteiro & Tourky, *The one-period
Gaussian Kyle model has exactly one equilibrium* (arXiv:2607.23585, **v3**
of 2026-08-10), over the definitions in `KyleUniqueness.Definitions`. The
statements themselves are the claimable artifact and are catalogued, with a
paper-to-Lean map and a fidelity assessment, in `STATEMENT_NOTES.md` at the
repository root. This file is `sorry`-free.

## Moved to `KyleUniqueness.Main`

Six headline carriers used to live here. They now sit at the top of the
import DAG, because their proofs consume the Session-3 modules
(`ValueFunction`, `Posterior`, `Resampling`, `Loss`, `Accounting`,
`SignedRoot`), every one of which imports this file:

* `isGammaSolution_zero_iff` — **Theorem 4** (v4 Theorem 7.1): `φ` satisfies
  the pointwise maximisation condition (17), `φ(v) ∈ argmax_x x(v − F(x))`
  for every `v ∈ ℝ`, iff `φ = id`;
* `existsUnique_zeroSolution` — its `∃!`-packaging;
* `isEquilibrium_eq_kyleStrategy` — the uniqueness direction of Theorem 1's
  strategy half (the development's only remaining open obligation);
* `kyle_unique_equilibrium` / `kyle_existsUnique_equilibrium` — Theorem 1
  projected to strategies: `φ` is an equilibrium strategy iff
  `φ = kyleStrategy`; there is exactly one equilibrium strategy;
* `kyle_equilibrium_pair_iff` — **Theorem 1** (v3's headline, the pair
  form): a pair `(φ, P)` is an equilibrium iff `φ` is Kyle's affine
  strategy `φ(v) = (σ/τ)(v − μ₀)` (eq. (1)) and `P(Y_φ) = μ₀ + λ·Y_φ`
  almost surely with `λ = τ/(2σ)` (eq. (2)).

## Main statements

* `kyleStrategy_isEquilibrium` /
  `kyleStrategy_kylePricingRule_isEquilibrium` — the existence direction of
  **Theorem 1** in its strategy and pair forms: Kyle's affine strategy
  (eq. (1)), paired with the affine pricing rule of eq. (2), is an
  equilibrium.
* `noiseTraderLoss_le_half` / `noiseTraderLoss_eq_half_iff` /
  `noiseTraderLoss_eq_neg_half_iff` / `integrable_noiseTraderLoss` —
  **Proposition 2**, the pivot of v3's proof: for EVERY Borel `φ`, the
  noise traders' expected loss `Γ = Cov(U, E[V ∣ Y])` (eq. (13)) is finite,
  `−1/2 ≤ Γ ≤ 1/2` (eq. (14)), with equality iff `φ(v) = ±v + a` for
  Lebesgue-a.e. `v` (eq. (15)).
* `lemma21_*` / `lemma22_memLp_two` / `lemma23_integrable` — **Lemmas
  2.1–2.3** (regularity of the inverse regression): the flow density is
  everywhere positive; the explicit `inverseRegression` is a genuine
  pricing rule (PROVED — the definitional-fidelity canary), continuous,
  square-integrable along the flow; the smoothing integrand is integrable.
* `equilibrium_iff_zeroSolution` — the `σ = τ = 1` case of the
  location–scale standardisation in the proof of Theorem 1 (§3.1):
  §1-equilibrium on the normalised model coincides with condition (17).
* `pricingRule_ae_eq_kylePricingRule` — a.s./Lebesgue-a.e. uniqueness of
  the pricing rule for the affine strategy (the pricing half of Theorem 1's
  uniqueness), with the classical "only continuous version" statement
  (`eq_kylePricingRule_of_continuous`) derived as a corollary.

The beyond-paper cubic-root layer (v2's deleted quadratic-cost family)
lives in `KyleUniqueness.BeyondPaper` and is NOT part of the v3 claim set.

All section, equation and lemma numbers refer to arXiv:2607.23585 **v3**.
-/

open MeasureTheory ProbabilityTheory

namespace KyleUniqueness

/-! ## Lemmas 2.1 and 2.2: regularity of the inverse regression

v3 §2.2 defines the pricing rule `P` by the explicit Bayes quotient
(our `inverseRegression`); Lemma 2.1 gives the everywhere-positive density
of `Y` (and the joint density of `(V, Y)`), and Lemma 2.2 asserts that `P`
is continuous with `P(Y) = E[V ∣ Y] ∈ L²` a.s. -/

/-- Lemma 2.1: the law of `Y = φ(V) + U` has the everywhere positive
density `p(y) = E[ϱ(y − φ(V))]`. (Positivity part; it also justifies the
division in `inverseRegression`.)

Proof: the integrand `v ↦ ϱ(y − φ(v))` is strictly positive everywhere
(`gaussianPDFReal_pos`), bounded (hence integrable against the probability
law of `V`), and its support is therefore all of `ℝ`, which has full
measure `1 > 0`. -/
theorem lemma21_flowDensity_pos {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    0 < flowDensity φ y := by
  simp only [flowDensity, stdNormalPDF]
  -- the integrand is bounded by `ϱ(0) = (√(2π))⁻¹`, so it is integrable
  -- against the probability law of `V`
  have hint : Integrable (fun v => gaussianPDFReal 0 1 (y - φ v))
      (gaussianReal 0 1) := by
    refine Integrable.mono'
      (integrable_const ((Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹))
      ((measurable_gaussianPDFReal 0 1).comp
        (measurable_const.sub hφ)).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le _ _ _
  rw [integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun v => gaussianPDFReal_nonneg 0 1 _) hint]
  -- the support of a strictly positive integrand is everything
  have hsupp : (Function.support fun v => gaussianPDFReal 0 1 (y - φ v))
      = Set.univ := by
    ext v
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne'
  rw [hsupp, measure_univ]
  norm_num

/-- **Lemma 2.2** (verbatim; the definitional-fidelity canary, PROVED): the
explicit posterior-mean formula `inverseRegression φ` is a pricing rule for
`φ` on the normalised model — i.e. it is Borel and `P(Y) = E[V ∣ Y]` almost
surely, for EVERY Borel strategy `φ`. This is the bridge between v3 §2.2's
Bayes-quotient definition of `P` and the abstract conditional expectation
of §1.

Proof: `inverseRegression φ = n/p` satisfies the density identity
`(n/p)·p = n` because `p > 0` everywhere (`lemma21_flowDensity_pos`), so
the general pricing-rule bridge
(`KyleModel.isPricingRule_of_forall_mul_flowPDF`, the Fubini/translation
argument that v3 App. A carries out for Lemma 2.2) applies on the
normalised model. -/
theorem lemma21_isPricingRule {φ : ℝ → ℝ} (hφ : Measurable φ) :
    stdModel.IsPricingRule φ (inverseRegression φ) := by
  refine stdModel.isPricingRule_of_forall_mul_flowPDF hφ
    (measurable_inverseRegression hφ) fun y => ?_
  -- the density identity `P·p = n`, i.e. `(n/p)·p = n`, from `p > 0`
  rw [stdModel_flowPDF, stdModel_flowNum, inverseRegression]
  exact div_mul_cancel₀ _ (lemma21_flowDensity_pos hφ y).ne'

/-- Lemma 2.2, continuity claim: `P` is continuous (v3 Lemma 4.1 proves
more — `P ∈ C¹` with `P′(y) = Cov_{π_y}(id, φ) > 0`, eq. (20)). -/
theorem lemma21_continuous {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Continuous (inverseRegression φ) := by
  -- Both `n` and `p` are continuous by dominated convergence (dominant:
  -- `ϱ ≤ ϱ(0)` resp. `|v|·ϱ(0)`, integrable against the Gaussian prior),
  -- and `p > 0` everywhere (Lemma 2.1), so the quotient is continuous.
  have hp : Continuous (flowDensity φ) := by
    have hrwp : flowDensity φ = fun y =>
        ∫ v, gaussianPDFReal 0 1 (y - φ v) ∂gaussianReal 0 1 := rfl
    rw [hrwp]
    refine continuous_of_dominated
      (bound := fun _ => (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹)
      (fun y => ((measurable_gaussianPDFReal 0 1).comp
        (measurable_const.sub hφ)).aestronglyMeasurable)
      (fun y => ae_of_all _ fun v => ?_) (integrable_const _)
      (ae_of_all _ fun v => ?_)
    · rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact gaussianPDFReal_le _ _ _
    · exact (continuous_gaussianPDFReal 0 1).comp
        (continuous_id.sub continuous_const)
  have hn : Continuous fun y => ∫ v, v * stdNormalPDF (y - φ v)
      ∂gaussianReal 0 1 := by
    simp only [stdNormalPDF]
    refine continuous_of_dominated
      (bound := fun v => |v| * (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹)
      (fun y => (measurable_id.mul ((measurable_gaussianPDFReal 0 1).comp
        (measurable_const.sub hφ))).aestronglyMeasurable)
      (fun y => ae_of_all _ fun v => ?_)
      (((integrable_id_gaussianReal 0 1).abs).mul_const _)
      (ae_of_all _ fun v => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg v)
      rw [abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact gaussianPDFReal_le _ _ _
    · exact continuous_const.mul ((continuous_gaussianPDFReal 0 1).comp
        (continuous_id.sub continuous_const))
  have hrw : inverseRegression φ = fun y =>
      (∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1) / flowDensity φ y :=
    rfl
  rw [hrw]
  exact hn.div hp fun y => (lemma21_flowDensity_pos hφ y).ne'

/-- Lemma 2.2, integrability claim: `P(Y) = E[V ∣ Y] ∈ L²` — the explicit
inverse regression is square-integrable along the order flow. (v3 proves it
by the conditional-Jensen/L²-contraction argument; it is the integrability
input to Proposition 2.) -/
theorem lemma22_memLp_two {φ : ℝ → ℝ} (hφ : Measurable φ) :
    MemLp (fun ω => inverseRegression φ (stdModel.orderFlow φ ω)) 2
      stdModel.μ := by
  -- `P(Y)` is a version of `E[V ∣ Y]` (the proved canary), and conditional
  -- expectation is an L²-contraction (`MemLp.condExp`) of `V ∈ L²`.
  have hV2 : MemLp stdModel.V 2 stdModel.μ := by
    have h : MemLp id 2 (stdModel.μ.map stdModel.V) := by
      rw [stdModel.map_V, stdModel_valueLaw]
      simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      stdModel.hV.aemeasurable).mp h
  have hc : MemLp (condExp (stdModel.flowSigma φ) stdModel.μ stdModel.V) 2
      stdModel.μ := MemLp.condExp one_le_two hV2
  exact MemLp.ae_eq (lemma21_isPricingRule hφ).ae_eq_condExp.symm hc

/-! ## Lemma 2.3: integrability of the smoothed price

v3 replaces v2's pointwise growth bound `|P(y)| ≤ |y| + K` (v2 eq. (4),
deleted) by an integrated statement: `P̃(x + U) ∈ L¹` for every Borel
version `P̃` and every `x`, proved in App. A by the `K_x` kernel-boundedness
argument. We state it for the canonical version; the general-version form
follows from a.e.-agreement of versions (`x + U` has a density). -/

/-- (Proof-internal, v3 App. A, Lemma 2.3.) Interval lower bound for the
flow density: `p(y) ≥ μφ([α,β]) · min(ϱ(y−α), ϱ(y−β))` where `μφ` is the
law of `φ(V)`. -/
private lemma flowDensity_ge_Icc {φ : ℝ → ℝ} (hφ : Measurable φ)
    (α β y : ℝ) :
    ((gaussianReal 0 1).map φ (Set.Icc α β)).toReal
        * min (stdNormalPDF (y - α)) (stdNormalPDF (y - β))
      ≤ flowDensity φ y := by
  have hint : Integrable (fun v => stdNormalPDF (y - φ v))
      (gaussianReal 0 1) := by
    simp only [stdNormalPDF]
    refine Integrable.mono'
      (integrable_const ((Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹))
      ((measurable_gaussianPDFReal 0 1).comp
        (measurable_const.sub hφ)).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le _ _ _
  have hs : MeasurableSet (φ ⁻¹' Set.Icc α β) := hφ measurableSet_Icc
  have hmass : (gaussianReal 0 1).map φ (Set.Icc α β)
      = (gaussianReal 0 1) (φ ⁻¹' Set.Icc α β) :=
    Measure.map_apply hφ measurableSet_Icc
  have h1 : ∫ _ in φ ⁻¹' Set.Icc α β,
        min (stdNormalPDF (y - α)) (stdNormalPDF (y - β)) ∂(gaussianReal 0 1)
      ≤ ∫ v in φ ⁻¹' Set.Icc α β, stdNormalPDF (y - φ v)
          ∂(gaussianReal 0 1) := by
    refine setIntegral_mono_on ((integrable_const _).integrableOn)
      hint.integrableOn hs fun v hv => ?_
    have hmem : φ v ∈ Set.Icc α β := hv
    have hcase : |y - φ v| ≤ |y - α| ∨ |y - φ v| ≤ |y - β| := by
      rcases le_or_gt 0 (y - φ v) with h | h
      · left
        rw [abs_of_nonneg h]
        exact le_trans (by linarith [hmem.1]) (le_abs_self _)
      · right
        rw [abs_of_neg h]
        exact le_trans (by linarith [hmem.2]) (neg_le_abs _)
    rcases hcase with h | h
    · exact le_trans (min_le_left _ _) (gaussianPDFReal_std_anti h)
    · exact le_trans (min_le_right _ _) (gaussianPDFReal_std_anti h)
  have h2 : ∫ v in φ ⁻¹' Set.Icc α β, stdNormalPDF (y - φ v)
        ∂(gaussianReal 0 1)
      ≤ flowDensity φ y := by
    rw [flowDensity]
    exact setIntegral_le_integral hint
      (ae_of_all _ fun v => gaussianPDFReal_nonneg _ _ _)
  calc ((gaussianReal 0 1).map φ (Set.Icc α β)).toReal
        * min (stdNormalPDF (y - α)) (stdNormalPDF (y - β))
      = ∫ _ in φ ⁻¹' Set.Icc α β,
          min (stdNormalPDF (y - α)) (stdNormalPDF (y - β))
          ∂(gaussianReal 0 1) := by
        rw [setIntegral_const, hmass, smul_eq_mul]
        rfl
    _ ≤ _ := le_trans h1 h2

/-- (Proof-internal.) A half-line `(x, ∞)` of positive measure contains a
compact interval `[α, β] ⊂ (x, ∞)` of positive measure. -/
private lemma exists_Icc_of_Ioi_ne_zero {ν : Measure ℝ} {x : ℝ}
    (h : ν (Set.Ioi x) ≠ 0) :
    ∃ α β : ℝ, x < α ∧ α ≤ β ∧ ν (Set.Icc α β) ≠ 0 := by
  have hcover : Set.Ioi x ⊆
      ⋃ n : ℕ, Set.Icc (x + 1 / (n + 1)) (x + (n + 1)) := by
    intro t ht
    have h0 : (0 : ℝ) < t - x := sub_pos.mpr ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h0
    obtain ⟨m, hm⟩ := exists_nat_ge (t - x)
    refine Set.mem_iUnion.mpr ⟨max n m, ?_, ?_⟩
    · have hle : (1 : ℝ) / (max n m + 1) ≤ 1 / (n + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have : (n : ℝ) ≤ (max n m : ℕ) := Nat.cast_le.mpr (le_max_left n m)
        linarith
      linarith
    · have : (m : ℝ) ≤ (max n m : ℕ) := Nat.cast_le.mpr (le_max_right n m)
      linarith
  by_contra hcon
  push Not at hcon
  refine h (measure_mono_null hcover (measure_iUnion_null fun n => ?_))
  have h1n : (0 : ℝ) < 1 / (n + 1) := by positivity
  refine hcon _ _ (by linarith) ?_
  have hle1 : (1 : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- (Proof-internal.) Mirror: a half-line `(−∞, x)` of positive measure
contains a compact interval `[α, β] ⊂ (−∞, x)` of positive measure. -/
private lemma exists_Icc_of_Iio_ne_zero {ν : Measure ℝ} {x : ℝ}
    (h : ν (Set.Iio x) ≠ 0) :
    ∃ α β : ℝ, β < x ∧ α ≤ β ∧ ν (Set.Icc α β) ≠ 0 := by
  have hcover : Set.Iio x ⊆
      ⋃ n : ℕ, Set.Icc (x - (n + 1)) (x - 1 / (n + 1)) := by
    intro t ht
    have h0 : (0 : ℝ) < x - t := sub_pos.mpr ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h0
    obtain ⟨m, hm⟩ := exists_nat_ge (x - t)
    refine Set.mem_iUnion.mpr ⟨max n m, ?_, ?_⟩
    · have : (m : ℝ) ≤ (max n m : ℕ) := Nat.cast_le.mpr (le_max_right n m)
      linarith
    · have hle : (1 : ℝ) / (max n m + 1) ≤ 1 / (n + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have : (n : ℝ) ≤ (max n m : ℕ) := Nat.cast_le.mpr (le_max_left n m)
        linarith
      linarith
  by_contra hcon
  push Not at hcon
  refine h (measure_mono_null hcover (measure_iUnion_null fun n => ?_))
  have h1n : (0 : ℝ) < 1 / (n + 1) := by positivity
  refine hcon _ _ (by linarith) ?_
  have hle1 : (1 : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- (Proof-internal, v3 App. A, Lemma 2.3.) The kernel bound: if `[α, β]`
carries positive `φ(V)`-mass and `a` lies on the same side of `x` as the
interval, then `K_x(a) ≤ r⁻¹(e^{(x−α)²} + e^{(x−β)²})`. -/
private lemma lintegral_kernel_le_Icc {φ : ℝ → ℝ} (hφ : Measurable φ)
    (x α β a : ℝ)
    (hr : (gaussianReal 0 1).map φ (Set.Icc α β) ≠ 0)
    (hα : 0 ≤ (α - x) * (a - x)) (hβ : 0 ≤ (β - x) * (a - x)) :
    (∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - a)
        / flowDensity φ y))
      ≤ ENNReal.ofReal
          ((((gaussianReal 0 1).map φ (Set.Icc α β)).toReal)⁻¹
            * (Real.exp ((x - α) ^ 2) + Real.exp ((x - β) ^ 2))) := by
  set r : ℝ := ((gaussianReal 0 1).map φ (Set.Icc α β)).toReal with hr_def
  have hrpos : 0 < r := ENNReal.toReal_pos hr (measure_ne_top _ _)
  -- pointwise domination by the two shifted-Gaussian kernels
  have hpt : ∀ y : ℝ, stdNormalPDF (y - x) * stdNormalPDF (y - a)
        / flowDensity φ y
      ≤ r⁻¹ * (stdNormalPDF (y - x) * stdNormalPDF (y - a)
            / stdNormalPDF (y - α)
          + stdNormalPDF (y - x) * stdNormalPDF (y - a)
            / stdNormalPDF (y - β)) := by
    intro y
    have hppos := lemma21_flowDensity_pos hφ y
    have hnum : (0 : ℝ) ≤ stdNormalPDF (y - x) * stdNormalPDF (y - a) :=
      mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
    have hαpos : (0 : ℝ) < stdNormalPDF (y - α) :=
      gaussianPDFReal_pos 0 1 _ one_ne_zero
    have hβpos : (0 : ℝ) < stdNormalPDF (y - β) :=
      gaussianPDFReal_pos 0 1 _ one_ne_zero
    have hplow := flowDensity_ge_Icc hφ α β y
    rw [← hr_def] at hplow
    rcases min_cases (stdNormalPDF (y - α)) (stdNormalPDF (y - β)) with
      ⟨hmin, _⟩ | ⟨hmin, _⟩ <;> rw [hmin] at hplow
    · -- min = ϱ(y − α)
      calc stdNormalPDF (y - x) * stdNormalPDF (y - a) / flowDensity φ y
          ≤ stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / (r * stdNormalPDF (y - α)) :=
            div_le_div_of_nonneg_left hnum (by positivity) hplow
        _ = r⁻¹ * (stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / stdNormalPDF (y - α)) := by
            field_simp
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_add_of_nonneg_right (div_nonneg hnum hβpos.le)
    · -- min = ϱ(y − β)
      calc stdNormalPDF (y - x) * stdNormalPDF (y - a) / flowDensity φ y
          ≤ stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / (r * stdNormalPDF (y - β)) :=
            div_le_div_of_nonneg_left hnum (by positivity) hplow
        _ = r⁻¹ * (stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / stdNormalPDF (y - β)) := by
            field_simp
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_add_of_nonneg_left (div_nonneg hnum hαpos.le)
  -- measurable pieces for the lintegral algebra
  have hkerα : Measurable fun y : ℝ => ENNReal.ofReal
      (stdNormalPDF (y - x) * stdNormalPDF (y - a) / stdNormalPDF (y - α)) := by
    simp only [stdNormalPDF]
    exact ((((measurable_gaussianPDFReal 0 1).comp
      (measurable_id.sub_const x)).mul ((measurable_gaussianPDFReal 0 1).comp
      (measurable_id.sub_const a))).div ((measurable_gaussianPDFReal 0 1).comp
      (measurable_id.sub_const α))).ennreal_ofReal
  have hkerβ : Measurable fun y : ℝ => ENNReal.ofReal
      (stdNormalPDF (y - x) * stdNormalPDF (y - a) / stdNormalPDF (y - β)) := by
    simp only [stdNormalPDF]
    exact ((((measurable_gaussianPDFReal 0 1).comp
      (measurable_id.sub_const x)).mul ((measurable_gaussianPDFReal 0 1).comp
      (measurable_id.sub_const a))).div ((measurable_gaussianPDFReal 0 1).comp
      (measurable_id.sub_const β))).ennreal_ofReal
  -- integrate the pointwise bound and evaluate the two kernels
  calc (∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - a)
        / flowDensity φ y))
      ≤ ∫⁻ y, ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / stdNormalPDF (y - α))
            + ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / stdNormalPDF (y - β))) := by
        refine lintegral_mono fun y => ?_
        refine le_trans (ENNReal.ofReal_le_ofReal (hpt y)) (le_of_eq ?_)
        have hA : (0 : ℝ) ≤ stdNormalPDF (y - x) * stdNormalPDF (y - a)
            / stdNormalPDF (y - α) :=
          div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
            (gaussianPDFReal_nonneg _ _ _))
            (gaussianPDFReal_pos 0 1 _ one_ne_zero).le
        have hB : (0 : ℝ) ≤ stdNormalPDF (y - x) * stdNormalPDF (y - a)
            / stdNormalPDF (y - β) :=
          div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
            (gaussianPDFReal_nonneg _ _ _))
            (gaussianPDFReal_pos 0 1 _ one_ne_zero).le
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hA hB]
    _ = ENNReal.ofReal r⁻¹
          * ((∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x)
              * stdNormalPDF (y - a) / stdNormalPDF (y - α)))
            + ∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x)
              * stdNormalPDF (y - a) / stdNormalPDF (y - β))) := by
        have hsum_meas : Measurable fun y : ℝ =>
            ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / stdNormalPDF (y - α))
            + ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - a)
              / stdNormalPDF (y - β)) := hkerα.add hkerβ
        rw [lintegral_const_mul _ hsum_meas, lintegral_add_left hkerα]
    _ ≤ ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (Real.exp ((x - α) ^ 2))
            + ENNReal.ofReal (Real.exp ((x - β) ^ 2))) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · have h := lintegral_gaussianPDFReal_std_mul_div x a α
          simp only [stdNormalPDF]
          rw [h]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          nlinarith [hα]
        · have h := lintegral_gaussianPDFReal_std_mul_div x a β
          simp only [stdNormalPDF]
          rw [h]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          nlinarith [hβ]
    _ = ENNReal.ofReal (r⁻¹ * (Real.exp ((x - α) ^ 2)
          + Real.exp ((x - β) ^ 2))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add
          (Real.exp_pos _).le (Real.exp_pos _).le]

/-- Lemma 2.3, integrability part (stated for the canonical version, in the
convolution form of eq. (4)): for every Borel `φ` and every `x`, the
integrand `y ↦ P(y)·ϱ(y − x)` of `F(x) = E[P(x + U)]` is Lebesgue
integrable. In particular the Bochner integral defining
`gaussianSmoothing` is the honest expectation. -/
theorem lemma23_integrable {φ : ℝ → ℝ} (hφ : Measurable φ) (x : ℝ) :
    Integrable (fun y => inverseRegression φ y * stdNormalPDF (y - x))
      (volume : Measure ℝ) := by
  have hppos : ∀ y, 0 < flowDensity φ y := lemma21_flowDensity_pos hφ
  have hpmeas : Measurable (flowDensity φ) := by
    have h := stdModel.measurable_flowPDF hφ
    rwa [show stdModel.flowPDF φ = flowDensity φ
      from funext (stdModel_flowPDF φ)] at h
  -- STEP 1: the kernel bound `K_x(φ(V)) ≤ C` a.s. (three cases, v3 App. A)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ᵐ v ∂(gaussianReal 0 1 : Measure ℝ),
      (∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - φ v)
        / flowDensity φ y)) ≤ ENNReal.ofReal C := by
    by_cases hIoi : (gaussianReal 0 1).map φ (Set.Ioi x) = 0
    · by_cases hIio : (gaussianReal 0 1).map φ (Set.Iio x) = 0
      · -- `μ = δ_x`: `p = ϱ(· − x)` and `K_x(x) = 1`
        refine ⟨1, ?_⟩
        have hae : ∀ᵐ v ∂(gaussianReal 0 1 : Measure ℝ), φ v = x := by
          have hcompl : (gaussianReal 0 1) (φ ⁻¹' {x}ᶜ) = 0 := by
            rw [← Measure.map_apply hφ (measurableSet_singleton x).compl,
              ← Set.Iio_union_Ioi]
            exact measure_union_null hIio hIoi
          rw [ae_iff]
          exact hcompl
        have hpx : ∀ y, flowDensity φ y = stdNormalPDF (y - x) := by
          intro y
          rw [flowDensity,
            integral_congr_ae (hae.mono fun v hv => by rw [hv])]
          simp
        filter_upwards [hae] with v hv
        rw [hv]
        have hker : ∀ y, stdNormalPDF (y - x) * stdNormalPDF (y - x)
            / flowDensity φ y = stdNormalPDF (y - x) := by
          intro y
          have hne : stdNormalPDF (y - x) ≠ 0 :=
            (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne'
          rw [hpx y, mul_div_assoc, div_self hne, mul_one]
        calc (∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x)
              * stdNormalPDF (y - x) / flowDensity φ y))
            = ∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x)) :=
              lintegral_congr fun y => by rw [hker y]
          _ = 1 := lintegral_ofReal_gaussianPDFReal_sub one_ne_zero x
          _ ≤ ENNReal.ofReal 1 := by rw [ENNReal.ofReal_one]
      · -- mass on the left only: a.e. `φ(v) ≤ x`, left interval
        obtain ⟨α, β, hβx, hαβ, hmass⟩ := exists_Icc_of_Iio_ne_zero hIio
        refine ⟨(((gaussianReal 0 1).map φ (Set.Icc α β)).toReal)⁻¹
          * (Real.exp ((x - α) ^ 2) + Real.exp ((x - β) ^ 2)), ?_⟩
        have haex : ∀ᵐ v ∂(gaussianReal 0 1 : Measure ℝ), φ v ≤ x := by
          have h0 : (gaussianReal 0 1) (φ ⁻¹' Set.Ioi x) = 0 := by
            rw [← Measure.map_apply hφ measurableSet_Ioi]
            exact hIoi
          rw [ae_iff]
          convert h0 using 2
          ext v
          simp [Set.mem_Ioi, not_le]
        filter_upwards [haex] with v hv
        refine lintegral_kernel_le_Icc hφ x α β (φ v) hmass ?_ ?_
        · nlinarith
        · nlinarith
    · by_cases hIio : (gaussianReal 0 1).map φ (Set.Iio x) = 0
      · -- mass on the right only: a.e. `φ(v) ≥ x`, right interval
        obtain ⟨α, β, hxα, hαβ, hmass⟩ := exists_Icc_of_Ioi_ne_zero hIoi
        refine ⟨(((gaussianReal 0 1).map φ (Set.Icc α β)).toReal)⁻¹
          * (Real.exp ((x - α) ^ 2) + Real.exp ((x - β) ^ 2)), ?_⟩
        have haex : ∀ᵐ v ∂(gaussianReal 0 1 : Measure ℝ), x ≤ φ v := by
          have h0 : (gaussianReal 0 1) (φ ⁻¹' Set.Iio x) = 0 := by
            rw [← Measure.map_apply hφ measurableSet_Iio]
            exact hIio
          rw [ae_iff]
          convert h0 using 2
          ext v
          simp [Set.mem_Iio, not_le]
        filter_upwards [haex] with v hv
        refine lintegral_kernel_le_Icc hφ x α β (φ v) hmass ?_ ?_
        · exact mul_nonneg (by linarith) (by linarith)
        · exact mul_nonneg (by linarith) (by linarith)
      · -- mass on both sides: bounded everywhere by the sum of both bounds
        obtain ⟨α, β, hxα, hαβ, hmass⟩ := exists_Icc_of_Ioi_ne_zero hIoi
        obtain ⟨α', β', hβ'x, hα'β', hmass'⟩ := exists_Icc_of_Iio_ne_zero hIio
        set Cp : ℝ := (((gaussianReal 0 1).map φ (Set.Icc α β)).toReal)⁻¹
          * (Real.exp ((x - α) ^ 2) + Real.exp ((x - β) ^ 2)) with hCp_def
        set Cm : ℝ := (((gaussianReal 0 1).map φ (Set.Icc α' β')).toReal)⁻¹
          * (Real.exp ((x - α') ^ 2) + Real.exp ((x - β') ^ 2)) with hCm_def
        have hCp0 : 0 ≤ Cp := by
          rw [hCp_def]; positivity
        have hCm0 : 0 ≤ Cm := by
          rw [hCm_def]; positivity
        refine ⟨Cp + Cm, ae_of_all _ fun v => ?_⟩
        rcases le_total x (φ v) with hvx | hvx
        · refine le_trans (lintegral_kernel_le_Icc hφ x α β (φ v) hmass
            (mul_nonneg (by linarith) (by linarith))
            (mul_nonneg (by linarith) (by linarith))) ?_
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · refine le_trans (lintegral_kernel_le_Icc hφ x α' β' (φ v) hmass'
            (by nlinarith) (by nlinarith)) ?_
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- STEP 2: the main estimate `E[|P(x+U)|] ≤ E[|V| K_x(φ(V))] ≤ C·E|V| < ∞`
  have hPmeas : Measurable (inverseRegression φ) :=
    measurable_inverseRegression hφ
  refine ⟨(hPmeas.mul ((measurable_gaussianPDFReal 0 1).comp
    (measurable_id.sub_const x))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  -- `q(y) := ∫ |v| ϱ(y − φ(v)) dγ(v)` and its integrability
  have hq_int : ∀ y : ℝ, Integrable (fun v => |v| * stdNormalPDF (y - φ v))
      (gaussianReal 0 1) := by
    intro y
    simp only [stdNormalPDF]
    refine Integrable.mono'
      (((integrable_id_gaussianReal 0 1).abs).mul_const
        ((Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹))
      ((measurable_id.abs.mul ((measurable_gaussianPDFReal 0 1).comp
        (measurable_const.sub hφ))).aestronglyMeasurable)
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le _ _ _) (abs_nonneg v)
  -- pointwise bound `‖P(y)ϱ(y−x)‖ₑ ≤ ofReal (q(y)·ϱ(y−x)/p(y))`
  have hpt : ∀ y : ℝ, ‖inverseRegression φ y * stdNormalPDF (y - x)‖ₑ
      ≤ ENNReal.ofReal ((∫ v, |v| * stdNormalPDF (y - φ v)
          ∂(gaussianReal 0 1)) * stdNormalPDF (y - x) / flowDensity φ y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hnn : (0 : ℝ) ≤ stdNormalPDF (y - x) :=
      gaussianPDFReal_nonneg 0 1 (y - x)
    rw [abs_mul, abs_of_nonneg hnn]
    have hP : |inverseRegression φ y|
        ≤ (∫ v, |v| * stdNormalPDF (y - φ v) ∂(gaussianReal 0 1))
          / flowDensity φ y := by
      rw [inverseRegression, abs_div, abs_of_pos (hppos y)]
      refine (div_le_div_iff_of_pos_right (hppos y)).mpr ?_
      calc |∫ v, v * stdNormalPDF (y - φ v) ∂(gaussianReal 0 1)|
          ≤ ∫ v, |v * stdNormalPDF (y - φ v)| ∂(gaussianReal 0 1) :=
            abs_integral_le_integral_abs
        _ = ∫ v, |v| * stdNormalPDF (y - φ v) ∂(gaussianReal 0 1) := by
            refine integral_congr_ae (ae_of_all _ fun v => ?_)
            dsimp only
            have hnn' : (0 : ℝ) ≤ stdNormalPDF (y - φ v) :=
              gaussianPDFReal_nonneg 0 1 (y - φ v)
            rw [abs_mul, abs_of_nonneg hnn']
    calc |inverseRegression φ y| * stdNormalPDF (y - x)
        ≤ ((∫ v, |v| * stdNormalPDF (y - φ v) ∂(gaussianReal 0 1))
            / flowDensity φ y) * stdNormalPDF (y - x) :=
          mul_le_mul_of_nonneg_right hP (gaussianPDFReal_nonneg _ _ _)
      _ = (∫ v, |v| * stdNormalPDF (y - φ v) ∂(gaussianReal 0 1))
            * stdNormalPDF (y - x) / flowDensity φ y := by ring
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  -- rewrite the majorant as an iterated lintegral and swap (Tonelli)
  have h3a : ∀ y : ℝ, ENNReal.ofReal ((∫ v, |v| * stdNormalPDF (y - φ v)
        ∂(gaussianReal 0 1)) * stdNormalPDF (y - x) / flowDensity φ y)
      = ∫⁻ v, ENNReal.ofReal |v|
          * ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - φ v)
            / flowDensity φ y) ∂(gaussianReal 0 1) := by
    intro y
    have hc : (0 : ℝ) ≤ stdNormalPDF (y - x) / flowDensity φ y :=
      div_nonneg (gaussianPDFReal_nonneg _ _ _) (hppos y).le
    have h1 : (∫ v, |v| * stdNormalPDF (y - φ v) ∂(gaussianReal 0 1))
        * stdNormalPDF (y - x) / flowDensity φ y
        = ∫ v, (stdNormalPDF (y - x) / flowDensity φ y)
            * (|v| * stdNormalPDF (y - φ v)) ∂(gaussianReal 0 1) := by
      rw [integral_const_mul]
      ring
    rw [h1, ofReal_integral_eq_lintegral_ofReal ((hq_int y).const_mul _)
      (ae_of_all _ fun v => mul_nonneg hc (mul_nonneg (abs_nonneg v)
        (gaussianPDFReal_nonneg _ _ _)))]
    refine lintegral_congr fun v => ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg v)]
    congr 1
    ring
  rw [lintegral_congr h3a]
  have hswapmeas : AEMeasurable (Function.uncurry fun (y v : ℝ) =>
      ENNReal.ofReal |v| * ENNReal.ofReal (stdNormalPDF (y - x)
        * stdNormalPDF (y - φ v) / flowDensity φ y))
      ((volume : Measure ℝ).prod (gaussianReal 0 1)) := by
    refine Measurable.aemeasurable ?_
    simp only [stdNormalPDF]
    exact ((measurable_snd.abs).ennreal_ofReal).mul
      (((((measurable_gaussianPDFReal 0 1).comp
        (measurable_fst.sub_const x)).mul
        ((measurable_gaussianPDFReal 0 1).comp
          (measurable_fst.sub (hφ.comp measurable_snd)))).div
        (hpmeas.comp measurable_fst)).ennreal_ofReal)
  rw [lintegral_lintegral_swap hswapmeas]
  -- pull `|v|` out of the inner integral
  have h3c : ∀ v : ℝ, (∫⁻ y, ENNReal.ofReal |v|
      * ENNReal.ofReal (stdNormalPDF (y - x) * stdNormalPDF (y - φ v)
        / flowDensity φ y))
      = ENNReal.ofReal |v| * ∫⁻ y, ENNReal.ofReal (stdNormalPDF (y - x)
          * stdNormalPDF (y - φ v) / flowDensity φ y) := by
    intro v
    have hm : Measurable fun y : ℝ => ENNReal.ofReal (stdNormalPDF (y - x)
        * stdNormalPDF (y - φ v) / flowDensity φ y) := by
      simp only [stdNormalPDF]
      exact ((((measurable_gaussianPDFReal 0 1).comp
        (measurable_id.sub_const x)).mul
        ((measurable_gaussianPDFReal 0 1).comp
          (measurable_id.sub_const (φ v)))).div hpmeas).ennreal_ofReal
    exact lintegral_const_mul _ hm
  rw [lintegral_congr h3c]
  -- bound by `C · E|V| < ∞`
  have hEabs : (∫⁻ v, ENNReal.ofReal |v| ∂(gaussianReal 0 1)) < ⊤ := by
    have h := (integrable_id_gaussianReal 0 1).2
    rw [hasFiniteIntegral_def] at h
    refine lt_of_eq_of_lt (lintegral_congr fun v => ?_) h
    rw [Real.enorm_eq_ofReal_abs]
    rfl
  calc ∫⁻ v, (ENNReal.ofReal |v| * ∫⁻ y, ENNReal.ofReal
        (stdNormalPDF (y - x) * stdNormalPDF (y - φ v) / flowDensity φ y))
        ∂(gaussianReal 0 1)
      ≤ ∫⁻ v, ENNReal.ofReal |v| * ENNReal.ofReal C ∂(gaussianReal 0 1) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hC] with v hv
        exact mul_le_mul' le_rfl hv
    _ = (∫⁻ v, ENNReal.ofReal |v| ∂(gaussianReal 0 1)) * ENNReal.ofReal C := by
        have hm : Measurable fun v : ℝ => ENNReal.ofReal |v| :=
          measurable_id.abs.ennreal_ofReal
        exact lintegral_mul_const _ hm
    _ < ⊤ := ENNReal.mul_lt_top hEabs ENNReal.ofReal_lt_top

/-! ## Auxiliary: uniqueness of the continuous version

v3 phrases all pricing-rule uniqueness a.s. / up to Lebesgue-null
modification (Theorem 1, eq. (2); the intro remark on the a.e. variant);
the "unique continuous version" formulation below is v2 legacy. It remains
true, still feeds `eq_kylePricingRule_of_continuous`, and is kept as an
AUXILIARY statement — not paper-claim surface. -/

/-- Auxiliary (v2 legacy, demoted): `inverseRegression φ` is the UNIQUE
continuous pricing rule for `φ` on the normalised model — any continuous
pricing rule coincides with it. (Uses that the law of `Y` has everywhere
positive density.) -/
theorem lemma21_unique_continuous_version {φ : ℝ → ℝ} (hφ : Measurable φ)
    {Q : ℝ → ℝ} (hQc : Continuous Q)
    (hQ : stdModel.IsPricingRule φ Q) : Q = inverseRegression φ := by
  -- Flow-a.s. agreement transfers to Lebesgue-a.e. agreement (the flow
  -- density is everywhere positive, Lemma 2.1), and two continuous
  -- functions that agree Lebesgue-a.e. agree everywhere.
  have hae : Q =ᵐ[(volume : Measure ℝ)] inverseRegression φ :=
    stdModel.pricingRule_ae_eq_of_flowPDF_pos hφ hQ
      (lemma21_isPricingRule hφ)
      fun y => by rw [stdModel_flowPDF]; exact lemma21_flowDensity_pos hφ y
  exact (hQc.ae_eq_iff_eq (volume : Measure ℝ) (lemma21_continuous hφ)).mp hae

/-! ## The location–scale bridge at `σ = τ = 1` (proof of Theorem 1, §3.1)

Kyle's §1 equilibrium condition on the normalised model is EXACTLY v3's
pointwise-maximisation condition (17): expanding the profit expectation by
Fubini, `E[(v − P(x+U))x] = x(v − F(x))` for any pricing-rule version `P`,
and `F` is version-independent (Lemmas 2.2/2.3). This is the `σ = τ = 1`
instance of the standardisation step in the proof of Theorem 1 (§3.1), and
it certifies that `IsGammaSolution 0` — the hypothesis of Theorem 4 —
faithfully renders "equilibrium strategy" on the normalised model. -/

/-- On the normalised model, `φ` is an equilibrium strategy (§1) iff `φ`
satisfies the pointwise-maximisation condition (17) (i.e. is a
`0`-solution). -/
theorem equilibrium_iff_zeroSolution (φ : ℝ → ℝ) :
    stdModel.IsEquilibriumStrategy φ ↔ IsGammaSolution 0 φ := by
  -- The computational core (§3.1 at σ = τ = 1): against ANY pricing rule
  -- for `φ`, the insider's expected profit is `x(v − F(x))` — Fubini plus
  -- the version-independence of Lemmas 2.2/2.3.
  have key : ∀ (hφ : Measurable φ) (P : ℝ → ℝ),
      stdModel.IsPricingRule φ P → ∀ v x : ℝ,
      stdModel.expectedProfit P v x = objective 0 φ v x := by
    intro hφ P hP v x
    -- reduce to the canonical version (`P = inverseRegression φ` Leb-a.e.)
    have hae : P =ᵐ[(volume : Measure ℝ)] inverseRegression φ :=
      stdModel.pricingRule_ae_eq_of_flowPDF_pos hφ hP
        (lemma21_isPricingRule hφ)
        fun y => by rw [stdModel_flowPDF]; exact lemma21_flowDensity_pos hφ y
    -- version-independence of the profit (the argument of
    -- `expectedProfit_congr_ae` below, inlined at `stdModel` since that
    -- lemma is stated later in this file): `x + U` has a density.
    have hcongr : stdModel.expectedProfit P v x
        = stdModel.expectedProfit (inverseRegression φ) v x := by
      unfold KyleModel.expectedProfit
      refine integral_congr_ae ?_
      have hac : stdModel.μ.map (fun ω => x + stdModel.U ω)
          ≪ (volume : Measure ℝ) := by
        rw [show (fun ω => x + stdModel.U ω) = ((x + ·) ∘ stdModel.U)
            from rfl,
          ← Measure.map_map (measurable_const_add x) stdModel.hU,
          stdModel.map_U, KyleModel.noiseLaw, gaussianReal_map_const_add]
        exact gaussianReal_absolutelyContinuous _ stdModel.noiseVar_ne_zero
      have hcomp := ae_eq_comp' (μ := stdModel.μ)
        (f := fun ω => x + stdModel.U ω)
        (measurable_const.add stdModel.hU).aemeasurable hae hac
      filter_upwards [hcomp] with ω hω
      simp only [Function.comp_apply] at hω
      rw [hω]
    rw [hcongr]
    -- `P₀(x + U) ∈ L¹` (Lemma 2.3 = R1) after translating the integrand
    have hint23 := lemma23_integrable hφ x
    have hshift : Integrable (fun u => inverseRegression φ (x + u))
        (gaussianReal 0 1) := by
      rw [integrable_gaussianReal_iff one_ne_zero]
      have h1 : Integrable (fun u => inverseRegression φ (u + x)
          * stdNormalPDF (u + x - x)) (volume : Measure ℝ) :=
        hint23.comp_add_right x
      have h2 : (fun u => inverseRegression φ (u + x)
            * stdNormalPDF (u + x - x))
          = fun u => gaussianPDFReal 0 1 u * inverseRegression φ (x + u) := by
        funext u
        simp only [stdNormalPDF]
        rw [show u + x - x = u by ring, show u + x = x + u by ring, mul_comm]
      rwa [h2] at h1
    have hintU : Integrable
        (fun ω => inverseRegression φ (x + stdModel.U ω)) stdModel.μ := by
      have h := (integrable_map_measure
        (((measurable_inverseRegression hφ).comp
          (measurable_const_add x)).aestronglyMeasurable)
        stdModel.hU.aemeasurable).mp
        (by rw [stdModel.map_U, stdModel_noiseLaw]; exact hshift)
      exact h
    -- expand the profit integral
    rw [KyleModel.expectedProfit]
    have hrw : (fun ω => (v - inverseRegression φ (x + stdModel.U ω)) * x)
        = fun ω => v * x - x * inverseRegression φ (x + stdModel.U ω) := by
      funext ω; ring
    have hconst : Integrable (fun _ : ℝ × ℝ => v * x) stdModel.μ :=
      integrable_const _
    have hxP : Integrable
        (fun ω => x * inverseRegression φ (x + stdModel.U ω)) stdModel.μ :=
      hintU.const_mul x
    rw [hrw, integral_sub hconst hxP, integral_const, integral_const_mul]
    -- `E[P₀(x + U)] = F(x)` (definitionally, after pushing along `U`)
    have hF : ∫ ω, inverseRegression φ (x + stdModel.U ω) ∂stdModel.μ
        = gaussianSmoothing φ x := by
      rw [show (∫ ω, inverseRegression φ (x + stdModel.U ω) ∂stdModel.μ)
          = ∫ u, inverseRegression φ (x + u) ∂(stdModel.μ.map stdModel.U)
        from (integral_map stdModel.hU.aemeasurable
          (((measurable_inverseRegression hφ).comp
            (measurable_const_add x)).aestronglyMeasurable)).symm,
        stdModel.map_U, stdModel_noiseLaw]
      rfl
    rw [hF, objective]
    simp only [probReal_univ, one_smul]
    ring
  constructor
  · rintro ⟨hφ, P, hP, hmax⟩
    refine ⟨hφ, fun v x => ?_⟩
    rw [← key hφ P hP v x, ← key hφ P hP v (φ v)]
    exact hmax v x
  · rintro ⟨hφ, hmax⟩
    refine ⟨hφ, inverseRegression φ, lemma21_isPricingRule hφ, fun v x => ?_⟩
    rw [key hφ _ (lemma21_isPricingRule hφ) v x,
      key hφ _ (lemma21_isPricingRule hφ) v (φ v)]
    exact hmax v x

/-- Sanity: on the normalised model (`μ₀ = 0`, `τ = σ = 1`), Kyle's affine
strategy (eq. (1)) is the identity — the form appearing in Theorem 4.
Proved by unfolding; no `sorry`. -/
theorem stdModel_kyleStrategy : stdModel.kyleStrategy = id := by
  funext v
  simp [stdModel, KyleModel.kyleStrategy]

/-! ## Gaussian regression for affine strategies

The computational inputs to the proofs of Theorems 4 and 1: if `φ` is
affine with unit slope, `(V, Y)` is jointly Gaussian and the inverse
regression and its smoothing are the explicit affine maps below. (These
specialise v2's deleted general-`γ` price formulas to the only case v3
uses.) -/

/-- Gaussian regression, intercept form (used in the proof of Theorem 4
with the a.e. output `φ = v + a` of Proposition 2): for the affine strategy
`v ↦ v + a`, the inverse regression is `y ↦ (y − a)/2`. -/
theorem inverseRegression_affine (a : ℝ) :
    inverseRegression (fun v => v + a) = fun y => (y - a) / 2 := by
  -- Complete the square (`gaussianPDFReal_mul_gaussianPDFReal_std`, the
  -- `σ = τ = 1` Kyle factorization): the joint density of `(V, Y)` at
  -- `Y = V + a + U` factorizes as `ϱ_{0,2}(y − a) · ϱ_{(y−a)/2, 1/2}(v)`,
  -- so the Bayes quotient `n/p` is the posterior mean `(y − a)/2` (v3
  -- eq. (6) for the unit-slope affine strategy).
  funext y
  simp only [inverseRegression, flowDensity, stdNormalPDF]
  have hhalf : ((1 / 2 : NNReal)) ≠ 0 := by norm_num
  have h2 : ((2 : NNReal)) ≠ 0 := by norm_num
  -- the complete-the-square, shifted by `a`
  have hkey : ∀ v : ℝ,
      gaussianPDFReal 0 1 (y - (v + a)) * gaussianPDFReal 0 1 v
        = gaussianPDFReal 0 2 (y - a)
            * gaussianPDFReal ((y - a) / 2) (1 / 2) v := by
    intro v
    have h := gaussianPDFReal_mul_gaussianPDFReal_std (y - a) v
    rwa [show y - a - v = y - (v + a) by ring] at h
  -- numerator: `n(y) = ϱ_{0,2}(y − a) · (y − a)/2`
  have hnum : (∫ v, v * gaussianPDFReal 0 1 (y - (v + a)) ∂gaussianReal 0 1)
      = gaussianPDFReal 0 2 (y - a) * ((y - a) / 2) := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    calc ∫ v, gaussianPDFReal 0 1 v • (v * gaussianPDFReal 0 1 (y - (v + a)))
        = ∫ v, gaussianPDFReal 0 2 (y - a)
            * (v * gaussianPDFReal ((y - a) / 2) (1 / 2) v) := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          dsimp only
          rw [smul_eq_mul, show gaussianPDFReal 0 1 v *
              (v * gaussianPDFReal 0 1 (y - (v + a)))
              = v * (gaussianPDFReal 0 1 (y - (v + a))
                  * gaussianPDFReal 0 1 v) by ring, hkey v]
          ring
      _ = gaussianPDFReal 0 2 (y - a) * ((y - a) / 2) := by
          rw [integral_const_mul, integral_id_mul_gaussianPDFReal _ hhalf]
  -- denominator: `p(y) = ϱ_{0,2}(y − a)`
  have hden : (∫ v, gaussianPDFReal 0 1 (y - (v + a)) ∂gaussianReal 0 1)
      = gaussianPDFReal 0 2 (y - a) := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    calc ∫ v, gaussianPDFReal 0 1 v • gaussianPDFReal 0 1 (y - (v + a))
        = ∫ v, gaussianPDFReal 0 2 (y - a)
            * gaussianPDFReal ((y - a) / 2) (1 / 2) v := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          dsimp only
          rw [smul_eq_mul, mul_comm, hkey v]
      _ = gaussianPDFReal 0 2 (y - a) := by
          rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hhalf,
            mul_one]
  rw [hnum, hden,
    mul_div_cancel_left₀ _ (gaussianPDFReal_pos 0 2 (y - a) h2).ne']

/-- Gaussian regression for the identity strategy: `P(y) = y/2` — v3
eq. (2) at `τ = σ = 1`, `μ = 0`. Derived from the intercept form at
`a = 0`; no `sorry` of its own. -/
theorem inverseRegression_id : inverseRegression id = fun y => y / 2 := by
  have h := inverseRegression_affine 0
  simpa [Function.id_def] using h

/-- Gaussian smoothing, intercept form: for the affine strategy
`v ↦ v + a`, `F(x) = (x − a)/2`. -/
theorem gaussianSmoothing_affine (a : ℝ) :
    gaussianSmoothing (fun v => v + a) = fun x => (x - a) / 2 := by
  -- `F(x) = E[P(x + U)] = E[(x + U − a)/2] = (x − a)/2` since `E[U] = 0`.
  funext x
  simp only [gaussianSmoothing, inverseRegression_affine]
  have hrw : (fun u : ℝ => (x + u - a) / 2)
      = fun u => (x - a) / 2 + (1 / 2) * u := by
    funext u; ring
  have hint : Integrable (fun u : ℝ => (1 / 2 : ℝ) * u) (gaussianReal 0 1) := by
    simpa using (integrable_id_gaussianReal 0 1).const_mul (1 / 2 : ℝ)
  rw [hrw, integral_add (integrable_const _) hint, integral_const,
    integral_const_mul, integral_id_gaussianReal]
  simp

/-- Gaussian smoothing for the identity strategy: `F(x) = x/2`. Derived
from the intercept form at `a = 0`; no `sorry` of its own. -/
theorem gaussianSmoothing_id : gaussianSmoothing id = fun x => x / 2 := by
  have h := gaussianSmoothing_affine 0
  simpa [Function.id_def] using h

/-! ## Proposition 2: the sharp bound on the noise traders' expected loss

The pivot of v3's proof. `Γ := Cov(U, E[V ∣ Y])` (eq. (13)) is the noise
traders' expected loss; `noiseTraderLoss` realises it through the explicit
inverse regression (`Γ = E[U·P(Y)]`, the unnumbered display in Prop 5's
proof; the identification with the covariance is Lemma 2.2 + `E[U] = 0`).
Proposition 2 holds for EVERY Borel `φ` — no equilibrium hypothesis. -/

/-- Proposition 2, finiteness: the integrand defining `Γ` is integrable for
every Borel `φ` (v3: "Γ is finite"; by conditional Jensen and
Cauchy–Schwarz from Lemma 2.2's `P(Y) ∈ L²`). This de-vacuates the junk
value of the Bochner integral in `noiseTraderLoss`. -/
theorem integrable_noiseTraderLoss {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Integrable (fun p : ℝ × ℝ => p.2 * inverseRegression φ (φ p.1 + p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  -- `U ∈ L²` and `P(Y) ∈ L²` (Lemma 2.2), so the product is integrable
  -- (Cauchy–Schwarz / `MemLp.integrable_mul`).
  have hU2 : MemLp stdModel.U 2 stdModel.μ := by
    have h : MemLp id 2 (stdModel.μ.map stdModel.U) := by
      rw [stdModel.map_U, stdModel_noiseLaw]
      simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      stdModel.hU.aemeasurable).mp h
  exact hU2.integrable_mul (lemma22_memLp_two hφ)

/-! ### Proof-internal moment layer for Proposition 2 (not claim surface) -/

private lemma memLp_two_fst' : MemLp stdModel.V 2 stdModel.μ := by
  have h : MemLp id 2 (stdModel.μ.map stdModel.V) := by
    rw [stdModel.map_V, stdModel_valueLaw]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    stdModel.hV.aemeasurable).mp h

private lemma memLp_two_snd' : MemLp stdModel.U 2 stdModel.μ := by
  have h : MemLp id 2 (stdModel.μ.map stdModel.U) := by
    rw [stdModel.map_U, stdModel_noiseLaw]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    stdModel.hU.aemeasurable).mp h

private lemma integral_fst_mul_snd' :
    ∫ ω, stdModel.V ω * stdModel.U ω ∂stdModel.μ = 0 := by
  have h := integral_prod_mul (μ := gaussianReal 0 1)
    (ν := gaussianReal 0 1) (f := fun x : ℝ => x) (g := fun x : ℝ => x)
  rw [integral_id_gaussianReal, mul_zero] at h
  exact h

private lemma integral_snd_mul_snd' :
    ∫ ω, stdModel.U ω * stdModel.U ω ∂stdModel.μ = 1 := by
  have hmap : ∫ ω, stdModel.U ω * stdModel.U ω ∂stdModel.μ
      = ∫ x, x * x ∂(stdModel.μ.map stdModel.U) :=
    (integral_map stdModel.hU.aemeasurable
      (measurable_id.mul measurable_id).aestronglyMeasurable).symm
  rw [hmap, stdModel.map_U, stdModel_noiseLaw,
    integral_mul_self_gaussianReal_std]

/-- (Proof-internal.) The full L² identity behind Proposition 2:
`E[(2M − V − sU)²] = 1 + s² − 4sΓ` for every real `s`. -/
private lemma integral_sq_kernel' {φ : ℝ → ℝ} (hφ : Measurable φ) (s : ℝ) :
    ∫ ω, (2 * inverseRegression φ (stdModel.orderFlow φ ω) - stdModel.V ω
        - s * stdModel.U ω) ^ 2 ∂stdModel.μ
      = 1 + s ^ 2 - 4 * s * noiseTraderLoss φ := by
  set Mf : ℝ × ℝ → ℝ :=
    fun ω => inverseRegression φ (stdModel.orderFlow φ ω) with hMf_def
  have hV2 : MemLp stdModel.V 2 stdModel.μ := memLp_two_fst'
  have hU2 : MemLp stdModel.U 2 stdModel.μ := memLp_two_snd'
  have hM2 : MemLp Mf 2 stdModel.μ := lemma22_memLp_two hφ
  have hMM : Integrable (fun ω => Mf ω * Mf ω) stdModel.μ :=
    hM2.integrable_mul hM2
  have hVV : Integrable (fun ω => stdModel.V ω * stdModel.V ω) stdModel.μ :=
    hV2.integrable_mul hV2
  have hUU : Integrable (fun ω => stdModel.U ω * stdModel.U ω) stdModel.μ :=
    hU2.integrable_mul hU2
  have hMV : Integrable (fun ω => Mf ω * stdModel.V ω) stdModel.μ :=
    hM2.integrable_mul hV2
  have hUM : Integrable (fun ω => stdModel.U ω * Mf ω) stdModel.μ :=
    hU2.integrable_mul hM2
  have hVU : Integrable (fun ω => stdModel.V ω * stdModel.U ω) stdModel.μ :=
    hV2.integrable_mul hU2
  have hEVV : ∫ ω, stdModel.V ω * stdModel.V ω ∂stdModel.μ = 1 := by
    have hmap : ∫ ω, stdModel.V ω * stdModel.V ω ∂stdModel.μ
        = ∫ x, x * x ∂(stdModel.μ.map stdModel.V) :=
      (integral_map stdModel.hV.aemeasurable
        (measurable_id.mul measurable_id).aestronglyMeasurable).symm
    rw [hmap, stdModel.map_V, stdModel_valueLaw,
      integral_mul_self_gaussianReal_std]
  have hproj : ∫ ω, Mf ω * stdModel.V ω ∂stdModel.μ
      = ∫ ω, Mf ω * Mf ω ∂stdModel.μ := by
    have hm : stdModel.flowSigma φ
        ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
      (stdModel.measurable_orderFlow hφ).comap_le
    have hMsm : StronglyMeasurable[stdModel.flowSigma φ] Mf :=
      ((measurable_inverseRegression hφ).comp
        (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have hMV' : Integrable (Mf * stdModel.V) stdModel.μ := hMV
    have hVint : Integrable stdModel.V stdModel.μ := stdModel.integrable_V
    have hpull := condExp_mul_of_stronglyMeasurable_left hMsm hMV' hVint
    have hcexp : Mf =ᵐ[stdModel.μ]
        condExp (stdModel.flowSigma φ) stdModel.μ stdModel.V :=
      (lemma21_isPricingRule hφ).ae_eq_condExp
    calc ∫ ω, Mf ω * stdModel.V ω ∂stdModel.μ
        = ∫ ω, condExp (stdModel.flowSigma φ) stdModel.μ
            (Mf * stdModel.V) ω ∂stdModel.μ := (integral_condExp hm).symm
      _ = ∫ ω, (Mf * condExp (stdModel.flowSigma φ) stdModel.μ
            stdModel.V) ω ∂stdModel.μ := integral_congr_ae hpull
      _ = ∫ ω, Mf ω * Mf ω ∂stdModel.μ := by
          refine integral_congr_ae ?_
          filter_upwards [hcexp] with ω h
          simp only [Pi.mul_apply]
          rw [← h]
  have h1 : (fun ω => (2 * Mf ω - stdModel.V ω - s * stdModel.U ω) ^ 2)
      = fun ω => 4 * (Mf ω * Mf ω) + (stdModel.V ω * stdModel.V ω)
          + s ^ 2 * (stdModel.U ω * stdModel.U ω)
          - 4 * (Mf ω * stdModel.V ω)
          - 4 * s * (stdModel.U ω * Mf ω)
          + 2 * s * (stdModel.V ω * stdModel.U ω) := by
    funext ω; ring
  have hI1 : Integrable (fun ω => 4 * (Mf ω * Mf ω)) stdModel.μ :=
    hMM.const_mul 4
  have hI3 : Integrable
      (fun ω => s ^ 2 * (stdModel.U ω * stdModel.U ω)) stdModel.μ :=
    hUU.const_mul (s ^ 2)
  have hI4 : Integrable
      (fun ω => 4 * (Mf ω * stdModel.V ω)) stdModel.μ :=
    hMV.const_mul 4
  have hI5 : Integrable
      (fun ω => 4 * s * (stdModel.U ω * Mf ω)) stdModel.μ :=
    hUM.const_mul (4 * s)
  have hI6 : Integrable
      (fun ω => 2 * s * (stdModel.V ω * stdModel.U ω)) stdModel.μ :=
    hVU.const_mul (2 * s)
  have hA : Integrable (fun ω => 4 * (Mf ω * Mf ω)
      + stdModel.V ω * stdModel.V ω) stdModel.μ := hI1.add hVV
  have hB : Integrable (fun ω => 4 * (Mf ω * Mf ω)
      + stdModel.V ω * stdModel.V ω
      + s ^ 2 * (stdModel.U ω * stdModel.U ω)) stdModel.μ := hA.add hI3
  have hC : Integrable (fun ω => 4 * (Mf ω * Mf ω)
      + stdModel.V ω * stdModel.V ω
      + s ^ 2 * (stdModel.U ω * stdModel.U ω)
      - 4 * (Mf ω * stdModel.V ω)) stdModel.μ := hB.sub hI4
  have hD : Integrable (fun ω => 4 * (Mf ω * Mf ω)
      + stdModel.V ω * stdModel.V ω
      + s ^ 2 * (stdModel.U ω * stdModel.U ω)
      - 4 * (Mf ω * stdModel.V ω)
      - 4 * s * (stdModel.U ω * Mf ω)) stdModel.μ := hC.sub hI5
  have hGamma : noiseTraderLoss φ
      = ∫ ω, stdModel.U ω * Mf ω ∂stdModel.μ := rfl
  rw [h1, integral_add hD hI6, integral_sub hC hI5, integral_sub hB hI4,
    integral_add hA hI3, integral_add hI1 hVV,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul,
    hproj, hEVV, integral_snd_mul_snd', integral_fst_mul_snd', ← hGamma]
  ring

/-- **Proposition 2, eq. (14)**: `−1/2 ≤ Γ ≤ 1/2` for EVERY Borel strategy
`φ`. (v3's proof is elementary L² algebra: `0 ≤ E[(X − sU)²]` with
`X = 2E[V∣Y] − V`, `s = ±1`, using conditional Jensen `E[M²] ≤ E[V²] = 1`
and the projection identity `E[VM] = E[M²]`.) -/
theorem noiseTraderLoss_le_half {φ : ℝ → ℝ} (hφ : Measurable φ) :
    |noiseTraderLoss φ| ≤ 1 / 2 := by
  -- v3's elementary L² argument: `0 ≤ E[(2M − V − sU)²] = 1 + s² − 4sΓ`
  -- (`integral_sq_kernel'`, from the projection identity `E[MV] = E[M²]`
  -- and the moment dictionary), taken at `s = ±1`.
  have hkey : ∀ s : ℝ, 0 ≤ 1 + s ^ 2 - 4 * s * noiseTraderLoss φ := by
    intro s
    have hnonneg : (0 : ℝ) ≤ ∫ ω, (2 * inverseRegression φ
        (stdModel.orderFlow φ ω) - stdModel.V ω - s * stdModel.U ω) ^ 2
        ∂stdModel.μ := integral_nonneg fun ω => sq_nonneg _
    rw [integral_sq_kernel' hφ s] at hnonneg
    linarith
  have h1 := hkey 1
  have h2 := hkey (-1)
  rw [abs_le]
  constructor <;> nlinarith [h1, h2]

/-! ### Proof-internal: the signed equality case of Proposition 2 -/

private lemma inverseRegression_neg_affine (a : ℝ) :
    inverseRegression (fun v => -v + a) = fun y => -((y - a) / 2) := by
  funext y
  simp only [inverseRegression, flowDensity, stdNormalPDF]
  have hhalf : ((1 / 2 : NNReal)) ≠ 0 := by norm_num
  have h2 : ((2 : NNReal)) ≠ 0 := by norm_num
  have hkey : ∀ v : ℝ,
      gaussianPDFReal 0 1 (y - (-v + a)) * gaussianPDFReal 0 1 v
        = gaussianPDFReal 0 2 (a - y)
            * gaussianPDFReal ((a - y) / 2) (1 / 2) v := by
    intro v
    have h := gaussianPDFReal_mul_gaussianPDFReal_std (a - y) v
    rwa [show a - y - v = -(y - (-v + a)) by ring,
      gaussianPDFReal_std_neg] at h
  have hnum : (∫ v, v * gaussianPDFReal 0 1 (y - (-v + a))
      ∂gaussianReal 0 1)
      = gaussianPDFReal 0 2 (a - y) * ((a - y) / 2) := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    calc ∫ v, gaussianPDFReal 0 1 v
          • (v * gaussianPDFReal 0 1 (y - (-v + a)))
        = ∫ v, gaussianPDFReal 0 2 (a - y)
            * (v * gaussianPDFReal ((a - y) / 2) (1 / 2) v) := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          dsimp only
          rw [smul_eq_mul, show gaussianPDFReal 0 1 v *
              (v * gaussianPDFReal 0 1 (y - (-v + a)))
              = v * (gaussianPDFReal 0 1 (y - (-v + a))
                  * gaussianPDFReal 0 1 v) by ring, hkey v]
          ring
      _ = gaussianPDFReal 0 2 (a - y) * ((a - y) / 2) := by
          rw [integral_const_mul, integral_id_mul_gaussianPDFReal _ hhalf]
  have hden : (∫ v, gaussianPDFReal 0 1 (y - (-v + a)) ∂gaussianReal 0 1)
      = gaussianPDFReal 0 2 (a - y) := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    calc ∫ v, gaussianPDFReal 0 1 v * gaussianPDFReal 0 1 (y - (-v + a))
        = ∫ v, gaussianPDFReal 0 2 (a - y)
            * gaussianPDFReal ((a - y) / 2) (1 / 2) v := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          dsimp only
          rw [mul_comm, hkey v]
      _ = gaussianPDFReal 0 2 (a - y) := by
          rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hhalf,
            mul_one]
  rw [hnum, hden,
    mul_div_cancel_left₀ _ (gaussianPDFReal_pos 0 2 (a - y) h2).ne']
  ring

private lemma noiseTraderLoss_eq_signed_iff {φ : ℝ → ℝ} (hφ : Measurable φ)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    noiseTraderLoss φ = s / 2 ↔
      ∃ a : ℝ, φ =ᵐ[(volume : Measure ℝ)] fun v => s * v + a := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  constructor
  · -- (⇒) rigidity: `E[(2M − V − sU)²] = 0`, eq. (16), Tonelli sections,
    -- translation invariance of Lebesgue measure
    intro hΓ
    have hzero : ∫ ω, (2 * inverseRegression φ (stdModel.orderFlow φ ω)
        - stdModel.V ω - s * stdModel.U ω) ^ 2 ∂stdModel.μ = 0 := by
      rw [integral_sq_kernel' hφ s, hΓ]
      nlinarith [hs2]
    have hmemsub : MemLp (fun ω =>
        2 * inverseRegression φ (stdModel.orderFlow φ ω) - stdModel.V ω
          - s * stdModel.U ω) 2 stdModel.μ :=
      (((lemma22_memLp_two hφ).const_mul 2).sub memLp_two_fst').sub
        (memLp_two_snd'.const_mul s)
    have hae0 := (integral_eq_zero_iff_of_nonneg
      (fun ω => sq_nonneg _) hmemsub.integrable_sq).mp hzero
    -- eq. (16), rearranged: a.e. `(v,u)`, `T(φ(v)+u) = φ(v) − sv` where
    -- `T y := y − 2sP(y)`
    have hae1 : ∀ᵐ ω ∂((gaussianReal 0 1).prod (gaussianReal 0 1) :
        Measure (ℝ × ℝ)),
        φ ω.1 + ω.2 - 2 * s * inverseRegression φ (φ ω.1 + ω.2)
          = φ ω.1 - s * ω.1 := by
      have hae0' : ∀ᵐ ω ∂((gaussianReal 0 1).prod (gaussianReal 0 1) :
          Measure (ℝ × ℝ)),
          (2 * inverseRegression φ (stdModel.orderFlow φ ω) - stdModel.V ω
            - s * stdModel.U ω) ^ 2 = (0 : ℝ × ℝ → ℝ) ω := hae0
      filter_upwards [hae0'] with ω h
      have h2 : 2 * inverseRegression φ (φ ω.1 + ω.2) - ω.1 - s * ω.2 = 0 :=
        sq_eq_zero_iff.mp h
      linear_combination (-s) * h2 - ω.2 * hs2
    -- Tonelli sections + push each section to Lebesgue and translate
    have hsec := Measure.ae_ae_of_ae_prod hae1
    have hTv : ∀ᵐ v ∂(gaussianReal 0 1 : Measure ℝ),
        (fun y => y - 2 * s * inverseRegression φ y)
          =ᵐ[(volume : Measure ℝ)] fun _ => φ v - s * v := by
      filter_upwards [hsec] with v hv
      have hu : ∀ᵐ u ∂(volume : Measure ℝ),
          φ v + u - 2 * s * inverseRegression φ (φ v + u)
            = φ v - s * v :=
        ae_volume_of_ae_gaussianReal one_ne_zero hv
      have hset : MeasurableSet {y : ℝ |
          y - 2 * s * inverseRegression φ y = φ v - s * v} :=
        measurableSet_eq_fun
          (measurable_id.sub
            ((measurable_inverseRegression hφ).const_mul (2 * s)))
          measurable_const
      have hmap : (volume : Measure ℝ).map (fun u => φ v + u) = volume :=
        map_add_left_eq_self volume (φ v)
      have h3 := (ae_map_iff (measurable_const_add (φ v)).aemeasurable
        hset).mpr hu
      rw [hmap] at h3
      exact h3
    -- extract one good `v₀` and read off the constant
    obtain ⟨v₀, hv₀⟩ := hTv.exists
    refine ⟨φ v₀ - s * v₀, ?_⟩
    have hconst : ∀ᵐ v ∂(gaussianReal 0 1 : Measure ℝ),
        φ v - s * v = φ v₀ - s * v₀ := by
      filter_upwards [hTv] with v hv
      have h2 : (fun _ : ℝ => φ v - s * v)
          =ᵐ[(volume : Measure ℝ)] fun _ => φ v₀ - s * v₀ :=
        hv.symm.trans hv₀
      obtain ⟨y, hy⟩ := h2.exists
      exact hy
    have hvol := ae_volume_of_ae_gaussianReal one_ne_zero hconst
    filter_upwards [hvol] with v hv
    linarith [hv]
  · -- (⇐) affine strategies: joint Gaussianity + the regression formula
    rintro ⟨a, hae⟩
    have haeγ : φ =ᵐ[(gaussianReal 0 1 : Measure ℝ)] fun v => s * v + a :=
      hae.filter_mono
        (gaussianReal_absolutelyContinuous _ one_ne_zero).ae_le
    -- the two inverse regressions agree pointwise (`n` and `p` are
    -- integrals of a.e.-equal integrands)
    have hIR : inverseRegression φ
        = inverseRegression (fun v => s * v + a) := by
      funext y
      simp only [inverseRegression, flowDensity]
      congr 1
      · refine integral_congr_ae (haeγ.mono fun v hv => ?_)
        have hv' : φ v = s * v + a := hv
        dsimp only
        rw [hv']
      · refine integral_congr_ae (haeγ.mono fun v hv => ?_)
        have hv' : φ v = s * v + a := hv
        dsimp only
        rw [hv']
    have hΓcongr : noiseTraderLoss φ
        = noiseTraderLoss (fun v => s * v + a) := by
      rw [noiseTraderLoss, noiseTraderLoss, hIR]
      refine integral_congr_ae ?_
      have hfst : ∀ᵐ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1) :
          Measure (ℝ × ℝ)), φ p.1 = s * p.1 + a := by
        have h2 : ∀ᵐ v ∂(((gaussianReal 0 1).prod
            (gaussianReal 0 1)).map (Prod.fst : ℝ × ℝ → ℝ)),
            φ v = s * v + a := by
          rw [MeasureTheory.measurePreserving_fst.map_eq]
          filter_upwards [haeγ] with v hv
          exact hv
        exact ae_of_ae_map measurable_fst.aemeasurable h2
      filter_upwards [hfst] with p hp
      rw [hp]
    rw [hΓcongr]
    -- the affine regression formula (N1 + its mirror)
    have hIRaff : inverseRegression (fun v => s * v + a)
        = fun y => s * (y - a) / 2 := by
      rcases hs with rfl | rfl
      · rw [show (fun v : ℝ => (1 : ℝ) * v + a) = fun v => v + a
            from funext fun v => by ring, inverseRegression_affine a]
        funext y; ring
      · rw [show (fun v : ℝ => (-1 : ℝ) * v + a) = fun v => -v + a
            from funext fun v => by ring, inverseRegression_neg_affine a]
        funext y; ring
    simp only [noiseTraderLoss, hIRaff]
    have hexp : (fun p : ℝ × ℝ => p.2 * (s * (s * p.1 + a + p.2 - a) / 2))
        = fun p => s ^ 2 / 2 * (p.1 * p.2) + s / 2 * (p.2 * p.2) := by
      funext p; ring
    have hVUint : Integrable (fun p : ℝ × ℝ => s ^ 2 / 2 * (p.1 * p.2))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h : Integrable (fun p : ℝ × ℝ => p.1 * p.2) stdModel.μ :=
        memLp_two_fst'.integrable_mul memLp_two_snd'
      exact h.const_mul _
    have hUUint : Integrable (fun p : ℝ × ℝ => s / 2 * (p.2 * p.2))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h : Integrable (fun p : ℝ × ℝ => p.2 * p.2) stdModel.μ :=
        memLp_two_snd'.integrable_mul memLp_two_snd'
      exact h.const_mul _
    have hEVU' : ∫ p : ℝ × ℝ, p.1 * p.2
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 0 :=
      integral_fst_mul_snd'
    have hEUU' : ∫ p : ℝ × ℝ, p.2 * p.2
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 :=
      integral_snd_mul_snd'
    rw [hexp, integral_add hVUint hUUint, integral_const_mul,
      integral_const_mul, hEVU', hEUU']
    ring

/-- **Proposition 2, eq. (15), upper saturation**: `Γ = 1/2` iff
`φ(v) = v + a` for Lebesgue-a.e. `v`, for some `a ∈ ℝ`. (v3's equality case
is a measure-theoretic rigidity argument: `2P(Y) = V + U` a.s. (eq. (16))
⇒ a jointly-a.e. identity ⇒ Tonelli sections + translation invariance of
Lebesgue measure ⇒ `φ(v) − v` constant a.e.) -/
theorem noiseTraderLoss_eq_half_iff {φ : ℝ → ℝ} (hφ : Measurable φ) :
    noiseTraderLoss φ = 1 / 2 ↔
      ∃ a : ℝ, φ =ᵐ[(volume : Measure ℝ)] fun v => v + a := by
  have h := noiseTraderLoss_eq_signed_iff hφ
    (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
  simpa only [one_mul] using h

/-- **Proposition 2, eq. (15), lower saturation**: `Γ = −1/2` iff
`φ(v) = −v + a` for Lebesgue-a.e. `v`, for some `a ∈ ℝ` (the mirrored case
`s = −1`). -/
theorem noiseTraderLoss_eq_neg_half_iff {φ : ℝ → ℝ} (hφ : Measurable φ) :
    noiseTraderLoss φ = -(1 / 2) ↔
      ∃ a : ℝ, φ =ᵐ[(volume : Measure ℝ)] fun v => -v + a := by
  have h := noiseTraderLoss_eq_signed_iff hφ
    (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
  simpa only [neg_mul, one_mul, neg_div] using h

/-! ## Theorem 1: the strategy layer -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Existence direction of **Theorem 1** (strategy layer): Kyle's affine
strategy `φ(v) = (σ/τ)(v − μ₀)` (eq. (1)) is an equilibrium strategy.
(The definitional-fidelity canary, PROVED. v3 supplies the textual proof of
this direction that v2 only asserted.)

Proof: the witness pricing rule is eq. (2)'s affine rule
`P(y) = μ₀ + λy`, `λ = τ/(2σ)`. It prices the affine strategy by the
complete-the-square density identity
(`KyleModel.kylePricingRule_mul_flowPDF` fed through the pricing-rule
bridge), and against it the insider's profit is the concave quadratic
`(v − μ₀ − λx)·x`, maximised at `x = (σ/τ)(v − μ₀)` for EVERY `v`
(`KyleModel.expectedProfit_kylePricingRule_le`). -/
theorem kyleStrategy_isEquilibrium (M : KyleModel Ω) :
    M.IsEquilibriumStrategy M.kyleStrategy :=
  ⟨M.measurable_kyleStrategy, M.kylePricingRule,
    M.isPricingRule_of_forall_mul_flowPDF M.measurable_kyleStrategy
      M.measurable_kylePricingRule M.kylePricingRule_mul_flowPDF,
    fun v x => M.expectedProfit_kylePricingRule_le v x⟩

/-! ## Eq. (2): Kyle's pricing rule and the price impact `λ = τ/(2σ)` -/

/-- Eq. (2): `P_φ(y) = μ₀ + λy` with `λ = τ/(2σ)` is a pricing rule for
Kyle's affine strategy (PROVED).

Proof: the affine pair satisfies the density identity `P·p = n` by
completing the square (`KyleModel.kylePricingRule_mul_flowPDF`), and the
pricing-rule bridge turns the density identity into the conditional
expectation property. -/
theorem isPricingRule_kylePricingRule (M : KyleModel Ω) :
    M.IsPricingRule M.kyleStrategy M.kylePricingRule :=
  M.isPricingRule_of_forall_mul_flowPDF M.measurable_kyleStrategy
    M.measurable_kylePricingRule M.kylePricingRule_mul_flowPDF

/-- Pricing half of **Theorem 1**'s uniqueness, a.e.-primary form (v3
states all pricing-rule uniqueness a.s. / up to Lebesgue-null
modification): any pricing rule for Kyle's affine strategy agrees with
eq. (2)'s affine rule Lebesgue-almost everywhere. (Along the flow the two
agree a.s. by definition of pricing rule; the law of the flow has
everywhere-positive density — Lemma 2.1 — so flow-a.s. transfers to
Lebesgue-a.e.) -/
theorem pricingRule_ae_eq_kylePricingRule (M : KyleModel Ω) {P : ℝ → ℝ}
    (hP : M.IsPricingRule M.kyleStrategy P) :
    P =ᵐ[(volume : Measure ℝ)] M.kylePricingRule := by
  -- Both rules price the affine strategy, so they agree a.s. along the flow;
  -- the law of the flow is the `flowPDF`-weighted Lebesgue measure
  -- (`KyleModel.map_orderFlow`) with everywhere-positive density
  -- `ϱ_{0,2σ²}` (`flowPDF_kyleStrategy`), so flow-null is Lebesgue-null.
  refine M.pricingRule_ae_eq_of_flowPDF_pos M.measurable_kyleStrategy hP
    (isPricingRule_kylePricingRule M) fun y => ?_
  rw [M.flowPDF_kyleStrategy y]
  exact gaussianPDFReal_pos _ _ _ fun h =>
    (mul_pos two_pos (pow_pos M.hσ 2)).ne' (congrArg NNReal.toReal h)

/-- Classical corollary (v2's "only continuous version" phrasing, kept):
any CONTINUOUS pricing rule for Kyle's affine strategy equals
`y ↦ μ₀ + (τ/(2σ)) y` everywhere. Derived from the a.e.-primary form
(continuous functions that agree Lebesgue-a.e. agree everywhere); no
`sorry` of its own. -/
theorem eq_kylePricingRule_of_continuous (M : KyleModel Ω) {Q : ℝ → ℝ}
    (hQc : Continuous Q) (hQ : M.IsPricingRule M.kyleStrategy Q) :
    Q = M.kylePricingRule := by
  have hkc : Continuous M.kylePricingRule := by
    unfold KyleModel.kylePricingRule
    fun_prop
  exact (hQc.ae_eq_iff_eq (volume : Measure ℝ) hkc).mp
    (pricingRule_ae_eq_kylePricingRule M hQ)

/-! ## Theorem 1: the pair form (v3's headline) — ingredients

v3's Theorem 1 is an iff over the (strategy, pricing-rule) PAIR — see
`KyleModel.IsEquilibrium`. The assembly itself is `kyle_equilibrium_pair_iff`
in `KyleUniqueness.Main`; it uses the easy direction below together with two
version-independence ingredients: pricing rules for the same strategy agree
a.s. along the flow (`pricingRule_ae_orderFlow`, immediate from `condExp`
a.e.-uniqueness), and expected profits are insensitive to Lebesgue-null
modification of the pricing rule (`expectedProfit_congr_ae`, since `x + U`
has a density — the content of v3's Lemmas 2.2/2.3 remark that profits do
not depend on the chosen Borel version). -/

/-- Kyle's affine pair — the strategy of eq. (1) with the pricing rule of
eq. (2) — is an equilibrium PAIR (the `(1)∧(2) ⇒ equilibrium` direction of
Theorem 1, pair form). Assembled from the canary-phase infrastructure; no
`sorry`. -/
theorem kyleStrategy_kylePricingRule_isEquilibrium (M : KyleModel Ω) :
    M.IsEquilibrium M.kyleStrategy M.kylePricingRule :=
  ⟨M.measurable_kyleStrategy, isPricingRule_kylePricingRule M,
    fun v x => M.expectedProfit_kylePricingRule_le v x⟩

/-- Version-independence along the flow: any two pricing rules for the same
strategy agree almost surely along the order flow (both are versions of
`E[V ∣ Y_φ]`). Immediate from `condExp` a.e.-uniqueness; no `sorry`. -/
theorem pricingRule_ae_orderFlow (M : KyleModel Ω) {φ P Q : ℝ → ℝ}
    (hP : M.IsPricingRule φ P) (hQ : M.IsPricingRule φ Q) :
    (fun ω => P (M.orderFlow φ ω)) =ᵐ[M.μ]
      fun ω => Q (M.orderFlow φ ω) :=
  hP.ae_eq_condExp.trans hQ.ae_eq_condExp.symm

/-- Version-independence of expected profit: pricing rules that agree
Lebesgue-a.e. yield identical expected profits at every `(v, x)` (the law
of `x + U` is Gaussian, hence absolutely continuous). This is the
version-independence remark that v3 promotes to Lemmas 2.2/2.3; no
`sorry`. -/
theorem expectedProfit_congr_ae (M : KyleModel Ω) {P Q : ℝ → ℝ}
    (h : P =ᵐ[(volume : Measure ℝ)] Q) (v x : ℝ) :
    M.expectedProfit P v x = M.expectedProfit Q v x := by
  unfold KyleModel.expectedProfit
  refine integral_congr_ae ?_
  have hac : M.μ.map (fun ω => x + M.U ω) ≪ (volume : Measure ℝ) := by
    rw [show (fun ω => x + M.U ω) = ((x + ·) ∘ M.U) from rfl,
      ← Measure.map_map (measurable_const_add x) M.hU, M.map_U,
      KyleModel.noiseLaw, gaussianReal_map_const_add]
    exact gaussianReal_absolutelyContinuous _ M.noiseVar_ne_zero
  have hcomp := ae_eq_comp' (μ := M.μ)
    (f := fun ω => x + M.U ω) (measurable_const.add M.hU).aemeasurable h hac
  filter_upwards [hcomp] with ω hω
  simp only [Function.comp_apply] at hω
  rw [hω]

end KyleUniqueness
