/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Regularity

/-!
# Noise-trader loss: the `Γ` identities (v4 Lemma 3.1 / 3.2; decision D5)

The `Γ`-layer of Monteiro & Tourky, *The one-period Gaussian Kyle model has
exactly one equilibrium* (arXiv:2607.23585, **v4** of 2026-08-20), §3.

v4 §3.1 defines the noise traders' expected loss as
`Γ := E[U(P(Y) − V)]` and Lemma 3.1 chains it through

`Γ = E[U(P(Y) − V)] = E[U·P(Y)] = Cov(U, E[V ∣ Y]) = E[F′(φ(V))]`.

The repo's `noiseTraderLoss` is the middle member `E[U·P(Y)]`, on the
canonical normalised space `ℝ × ℝ` (coordinates `(V, U)` under `γ ⊗ γ`,
`γ = gaussianReal 0 1`). This file supplies the three remaining links of
that chain and the two clauses of Lemma 3.2 that the repo's `objective`
packaging needs. (`Γ` finite — the Cauchy–Schwarz clause of Lemma 3.1 — is
already `integrable_noiseTraderLoss` in `Statement.lean`.)

## Main statements

* `integral_snd_mul_sub_fst_eq_noiseTraderLoss` (and its `stdModel`
  packaging `integral_noise_mul_sub_value_eq_noiseTraderLoss`) — **first
  equality**: v4's definiens `E[U(P(Y) − V)]` agrees with the repo's
  `E[U·P(Y)]`, because `E[UV] = 0` by independence;
* `covariance_noise_condExp_eq_noiseTraderLoss` — **second equality**:
  `Γ = Cov(U, E[V ∣ Y])` against Mathlib's `ProbabilityTheory.covariance`
  (this is the reading asserted in the docstring of `noiseTraderLoss`);
* `integrable_deriv_gaussianSmoothing_comp` — `F′(φ(V)) ∈ L¹`, the
  integrability clause attached to the last equality;
* `noiseTraderLoss_eq_integral_deriv` — **last equality**:
  `Γ = E[F′(φ(V))]`;
* `expectedProfit_inverseRegression` / `objective_eq_expectedProfit` —
  **v4 Lemma 3.2** in the canonical-version form: the insider's §1 expected
  profit against the canonical pricing rule is the normalised objective, so
  `Π(v) = objective 0 φ v (φ v)` is `stdModel.expectedProfit` at `x = φ(v)`;
* `integrable_inverseRegression_const_add` — the canonical-version case of
  v4 Lemma 2.3's version clause, `P(x + U) ∈ L¹`;
* `noiseTraderLoss_id` — the sanity oracle `Γ = 1/2` at `φ = id`.

## Route

The `Γ = E[F′(φ(V))]` link is **one Fubini step on `γ ⊗ γ`**, not the
conditioning argument the paper writes. The repo already has

* `integrable_noiseTraderLoss` (v4 Lemma 3.1's Cauchy–Schwarz clause, from
  `lemma22_memLp_two`: `U ∈ L²`, `P(Y) ∈ L²`, hence `U·P(Y) ∈ L¹`), and
* `deriv_gaussianSmoothing` + `deriv_gaussianSmoothing_eq_prob` (v4 eq.
  (2.3) = v3 eq. (5)): `F′(x) = ∫ u·P(x + u) ∂γ`.

So `v ↦ F′(φ(v))` is literally the inner slice `v ↦ ∫ u, g(v, u) ∂γ` of the
integrand `g(v, u) = u·P(φ(v) + u)` of `Γ`. `Integrable.integral_prod_left`
then gives the integrability clause and `integral_integral` the identity —
the paper's "conditioning on `V`" step `E[U·P(Y) ∣ V] = F′(φ(V))` a.s. is
exactly Fubini's statement about slices here, so no `condExp` and no
Tonelli/Cauchy–Schwarz re-derivation is needed. The covariance link is
`covariance_eq_sub` plus `E[U] = 0` (`KyleModel.integral_U`).

## Hypotheses beyond the paper

None. Every statement carries only `hφ : Measurable φ` (the paper's "Borel
`φ`"); no equilibrium, monotonicity or moment hypothesis is used. The one
deliberate deviation is *packaging*: the "for every Borel version `P̃` of
the inverse regression …" clauses of v4 Lemmas 2.3/3.1/3.2 are not
re-proved here — the repo discharges version-independence once and for all
upstream (`pricingRule_ae_eq_of_flowPDF_pos`, `expectedProfit_congr_ae`),
and every statement below is about the canonical version
`inverseRegression φ`.
-/

open MeasureTheory ProbabilityTheory

namespace KyleUniqueness

/-! ## v4 Lemma 3.1: `Γ = E[F′(φ(V))]`

The derivative `F′` from v4 eq. (2.3) (`deriv_gaussianSmoothing_eq_prob`),
composed with `φ`, is the inner Fubini slice of the `Γ` integrand. -/

/-- v4 eq. (2.3) in `deriv` packaging: `F′(x) = E[U·P(x + U)]`. -/
theorem deriv_gaussianSmoothing_eq_integral {φ : ℝ → ℝ} (hφ : Measurable φ)
    (x : ℝ) :
    deriv (gaussianSmoothing φ) x
      = ∫ u, u * inverseRegression φ (x + u) ∂gaussianReal 0 1 := by
  rw [deriv_gaussianSmoothing hφ x, deriv_gaussianSmoothing_eq_prob φ x]

/-- `v ↦ F′(φ(v))` is exactly the inner Fubini slice
`v ↦ ∫ u, u·P(φ(v) + u) ∂γ` of the integrand of `Γ` (v4 §3.1; the displays
of v4 §3 are unnumbered). -/
theorem deriv_gaussianSmoothing_comp_eq {φ : ℝ → ℝ} (hφ : Measurable φ) :
    (fun v => deriv (gaussianSmoothing φ) (φ v))
      = fun v => ∫ u, u * inverseRegression φ (φ v + u) ∂gaussianReal 0 1 :=
  funext fun v => deriv_gaussianSmoothing_eq_integral hφ (φ v)

/-- **v4 Lemma 3.1, integrability clause**: `F′(φ(V)) ∈ L¹` under the
standard normal law of `V`. (The paper deduces this from integrability of
`U·P(Y)`; here it is the Fubini slice statement
`Integrable.integral_prod_left` applied to `integrable_noiseTraderLoss`.) -/
theorem integrable_deriv_gaussianSmoothing_comp {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    Integrable (fun v => deriv (gaussianSmoothing φ) (φ v))
      (gaussianReal 0 1) := by
  rw [deriv_gaussianSmoothing_comp_eq hφ]
  exact (integrable_noiseTraderLoss hφ).integral_prod_left

/-- **v4 Lemma 3.1, last equality**: `Γ = E[F′(φ(V))]`, for every Borel
strategy `φ`. -/
theorem noiseTraderLoss_eq_integral_deriv {φ : ℝ → ℝ} (hφ : Measurable φ) :
    noiseTraderLoss φ
      = ∫ v, deriv (gaussianSmoothing φ) (φ v) ∂gaussianReal 0 1 := by
  rw [deriv_gaussianSmoothing_comp_eq hφ]
  exact (integral_integral (f := fun v u => u * inverseRegression φ (φ v + u))
    (integrable_noiseTraderLoss hφ)).symm

/-! ## v4 §3.1: the definiens `E[U(P(Y) − V)]` agrees with `E[U·P(Y)]` -/

/-- `U·V ∈ L¹` on the normalised space (independence + first moments). -/
private lemma integrable_snd_mul_fst_prod :
    Integrable (fun p : ℝ × ℝ => p.2 * p.1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  ((integrable_id_gaussianReal 0 1).mul_prod
    (integrable_id_gaussianReal 0 1)).congr
      (ae_of_all _ fun p => mul_comm p.1 p.2)

/-- `E[U·V] = 0`: the coordinates of the normalised model are independent
standard normals, so the cross moment vanishes. -/
private lemma integral_snd_mul_fst_prod :
    ∫ p : ℝ × ℝ, p.2 * p.1
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 0 := by
  have h : ∫ p : ℝ × ℝ, p.2 * p.1
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = ∫ p : ℝ × ℝ, p.1 * p.2
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integral_congr_ae (ae_of_all _ fun p => mul_comm p.2 p.1)
  rw [h, integral_prod_mul (f := fun x : ℝ => x) (g := fun y : ℝ => y),
    integral_id_gaussianReal, mul_zero]

/-- **v4 Lemma 3.1, first equality** (definiens agreement): v4 §3.1 defines
the noise-trader loss as `Γ := E[U(P(Y) − V)]`, the repo as `E[U·P(Y)]`
(`noiseTraderLoss`). The two agree, because `E[U·V] = 0` by independence. -/
theorem integral_snd_mul_sub_fst_eq_noiseTraderLoss {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ p : ℝ × ℝ, p.2 * (inverseRegression φ (φ p.1 + p.2) - p.1)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = noiseTraderLoss φ := by
  have hsplit : (fun p : ℝ × ℝ =>
        p.2 * (inverseRegression φ (φ p.1 + p.2) - p.1))
      = fun p : ℝ × ℝ =>
        p.2 * inverseRegression φ (φ p.1 + p.2) - p.2 * p.1 :=
    funext fun p => by ring
  rw [hsplit, integral_sub (integrable_noiseTraderLoss hφ)
    integrable_snd_mul_fst_prod, integral_snd_mul_fst_prod, sub_zero]
  rfl

/-- `Γ = E[U(P(Y) − V)]` in `stdModel` packaging (v4 §3.1's definiens,
spelled with the order flow `Y = φ(V) + U`). -/
theorem integral_noise_mul_sub_value_eq_noiseTraderLoss {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ ω, stdModel.U ω
        * (inverseRegression φ (stdModel.orderFlow φ ω) - stdModel.V ω)
        ∂stdModel.μ
      = noiseTraderLoss φ :=
  integral_snd_mul_sub_fst_eq_noiseTraderLoss hφ

/-! ### The covariance reading of `Γ` -/

/-- `Cov(X, ·)` depends on its second argument only through its a.e. class.
(Missing at the pin; needed to move from the canonical version `P(Y)` to
the `condExp` in which v4 §3.1 states the covariance form.) -/
private lemma covariance_congr_ae_right {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y Y' : Ω → ℝ} (h : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X, Y'; μ] := by
  have hI : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae h
  unfold ProbabilityTheory.covariance
  rw [hI]
  refine integral_congr_ae (h.mono fun ω hω => ?_)
  simp only [hω]

/-- `U ∈ L²` on the normalised space (the `L²` half of v4 Lemma 3.1's
Cauchy–Schwarz clause that is not already `lemma22_memLp_two`). -/
private lemma memLp_two_noise : MemLp stdModel.U 2 stdModel.μ := by
  have h : MemLp id 2 (stdModel.μ.map stdModel.U) := by
    rw [stdModel.map_U, stdModel_noiseLaw]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    stdModel.hU.aemeasurable).mp h

/-- **v4 Lemma 3.1, covariance form**: `Γ = Cov(U, E[V ∣ Y])` — the reading
of `Γ` recorded in the docstring of `noiseTraderLoss` (v4 §3.1 = v3
eq. (13)), against Mathlib's `ProbabilityTheory.covariance`. The step is
`E[U] = 0` plus the `L²` bounds, with `P(Y) = E[V ∣ Y]` almost surely
(`lemma21_isPricingRule`, the repo's definitional-fidelity canary). -/
theorem covariance_noise_condExp_eq_noiseTraderLoss {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    cov[stdModel.U, condExp (stdModel.flowSigma φ) stdModel.μ stdModel.V;
      stdModel.μ] = noiseTraderLoss φ := by
  rw [← covariance_congr_ae_right (lemma21_isPricingRule hφ).ae_eq_condExp,
    covariance_eq_sub memLp_two_noise (lemma22_memLp_two hφ),
    stdModel.integral_U, zero_mul, sub_zero]
  rfl

/-! ## v4 Lemma 3.2: the insider's conditional expected profit -/

/-- Lemma 2.3 in shifted form: `P(x + U) ∈ L¹` for the standard normal `U`
and every `x` (so `F(x) = E[P(x + U)]` is an honest expectation). -/
theorem integrable_inverseRegression_const_add {φ : ℝ → ℝ}
    (hφ : Measurable φ) (x : ℝ) :
    Integrable (fun u => inverseRegression φ (x + u)) (gaussianReal 0 1) := by
  rw [integrable_gaussianReal_iff one_ne_zero]
  have h1 : Integrable (fun u => inverseRegression φ (u + x)
      * stdNormalPDF (u + x - x)) (volume : Measure ℝ) :=
    (lemma23_integrable hφ x).comp_add_right x
  have h2 : (fun u => inverseRegression φ (u + x) * stdNormalPDF (u + x - x))
      = fun u => gaussianPDFReal 0 1 u * inverseRegression φ (x + u) := by
    funext u
    simp only [stdNormalPDF]
    rw [show u + x - x = u by ring, show u + x = x + u by ring, mul_comm]
  rwa [h2] at h1

/-- **v4 Lemma 3.2** (canonical-version form): against the canonical pricing
rule `P = inverseRegression φ`, the insider's §1 expected profit
`E[(v − P(x + U))x]` at signal `v` and order `x` is the normalised objective
`x(v − F(x))`. -/
theorem expectedProfit_inverseRegression {φ : ℝ → ℝ} (hφ : Measurable φ)
    (v x : ℝ) :
    stdModel.expectedProfit (inverseRegression φ) v x = objective 0 φ v x := by
  have hPm : Measurable fun u => inverseRegression φ (x + u) :=
    (measurable_inverseRegression hφ).comp (measurable_const_add x)
  have hintU : Integrable
      (fun ω => inverseRegression φ (x + stdModel.U ω)) stdModel.μ := by
    refine (integrable_map_measure hPm.aestronglyMeasurable
      stdModel.hU.aemeasurable).mp ?_
    rw [stdModel.map_U, stdModel_noiseLaw]
    exact integrable_inverseRegression_const_add hφ x
  have hF : ∫ ω, inverseRegression φ (x + stdModel.U ω) ∂stdModel.μ
      = gaussianSmoothing φ x := by
    rw [show (∫ ω, inverseRegression φ (x + stdModel.U ω) ∂stdModel.μ)
        = ∫ u, inverseRegression φ (x + u) ∂(stdModel.μ.map stdModel.U)
      from (integral_map stdModel.hU.aemeasurable
        hPm.aestronglyMeasurable).symm,
      stdModel.map_U, stdModel_noiseLaw]
    rfl
  rw [KyleModel.expectedProfit]
  have hrw : (fun ω => (v - inverseRegression φ (x + stdModel.U ω)) * x)
      = fun ω => v * x - x * inverseRegression φ (x + stdModel.U ω) :=
    funext fun ω => by ring
  rw [hrw, integral_sub (integrable_const (v * x)) (hintU.const_mul x),
    integral_const, integral_const_mul, hF, objective]
  simp only [probReal_univ, one_smul]
  ring

/-- **v4 Lemma 3.2 at the submitted order** `x = φ(v)`: the informed
trader's conditional expected profit `Π(v) = φ(v)(v − F(φ(v)))` — the
integrand of the value function, `objective 0 φ v (φ v)` — is the §1
expected profit of the order `φ(v)` against the canonical pricing rule.
(This is the pointwise identity that `equilibrium_iff_zeroSolution` uses
internally, exposed under a name.) -/
theorem objective_eq_expectedProfit {φ : ℝ → ℝ} (hφ : Measurable φ) (v : ℝ) :
    objective 0 φ v (φ v)
      = stdModel.expectedProfit (inverseRegression φ) v (φ v) :=
  (expectedProfit_inverseRegression hφ v (φ v)).symm

/-! ## Sanity oracle -/

/-- Sanity oracle for the Lemma 3.1 route: at `φ = id` the Gaussian
smoothing is `F(x) = x/2` (`gaussianSmoothing_id`), so `F′ ≡ 1/2` and
`Γ = E[F′(V)] = 1/2` — the upper endpoint of v4 Prop. 4.1's bound. -/
theorem noiseTraderLoss_id : noiseTraderLoss id = 1 / 2 := by
  have hd : ∀ v : ℝ, deriv (gaussianSmoothing id) (id v) = 1 / 2 := by
    intro v
    rw [gaussianSmoothing_id]
    simp
  rw [noiseTraderLoss_eq_integral_deriv measurable_id,
    integral_congr_ae (ae_of_all _ hd), integral_const]
  simp

end KyleUniqueness
