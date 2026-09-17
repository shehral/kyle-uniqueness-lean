/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Definitions
import KyleUniqueness.GaussianHelpers

/-!
# The pricing-rule bridge: from density identities to conditional expectations

The workhorse of the proof phase (blueprint node P1, direct route): for any
Kyle model (v4 §1) and any Borel strategy `φ`, a Borel candidate price
function `Q : ℝ → ℝ` is a pricing rule — `Q(Y_φ) = E[V ∣ Y_φ]` a.s., item 2
("market efficiency") of v4 §1's equilibrium definition — as soon as it
satisfies the pointwise *density identity*

`Q(y) · p_φ(y) = n_φ(y)` for every `y`,

where `p_φ(y) = E[ϱ_σ(y − φ(V))]` is the order-flow density and
`n_φ(y) = E[V·ϱ_σ(y − φ(V))]` its value-weighted counterpart (`flowPDF` and
`flowNum` below; v4 §2.2's `p` and `n` in the normalised model, Appendix A's
`C`/`D` up to a common factor). This is the Bayes-quotient description of
the inverse regression, verified against Mathlib's `condExp` through the
uniqueness characterisation `ae_eq_condExp_of_forall_setIntegral_eq`: for
every Borel `B ⊆ ℝ`,

`E[Q(Y)·1_B(Y)] = ∫ 1_B(y)·Q(y)·p_φ(y) dy = ∫ 1_B(y)·n_φ(y) dy
               = E[V·1_B(Y)]`,

each equality by Tonelli/Fubini and the translation
`∫ f(t+u) N(0,σ²)(du) = ∫ ϱ_σ(y−t)·f(y) dy` (`GaussianHelpers`).

The file ends with the consumers proved for the canary phase:

* `KyleModel.kylePricingRule_mul_flowPDF` — eq. (1.2)'s density identity for
  the affine pair (eqs. (1.1)/(1.2)), by the complete-the-square
  factorization `gaussianPDFReal_mul_gaussianPDFReal_kyle`;
* `KyleModel.expectedProfit_kylePricingRule` /
  `KyleModel.expectedProfit_kylePricingRule_le` — against the affine rule
  the insider's profit (v4 §1, item 1, untagged) is the strictly concave
  quadratic `(v − μ₀ − λx)·x`, maximised at
  `x = (σ/τ)(v − μ₀) = kyleStrategy v`;
* `stdModel_flowPDF` / `stdModel_flowNum` /
  `measurable_inverseRegression` — the σ = τ = 1 specialisations linking
  the general-model bridge to §2's normalised objects.

## Numbering: ONE declared scheme (v4), with the legacy table

This module's proofs predate both the v3 and the v4 reconciliations and its
comments once interleaved **v2** and **v3** numbers with no in-file key —
three schemes for a reader to disambiguate. That is fixed: **every section,
equation and lemma number below is arXiv:2607.23585 v4** (*The one-period
Kyle model has one equilibrium*, 2026-08-20). Legacy table for anyone
holding an older PDF:

| object | v2 | v3 | **v4** |
|---|---|---|---|
| insider's profit / profit maximisation | eq. (1) | display before eq. (1) | §1 item 1, untagged |
| Kyle's strategy `φ(v) = (σ/τ)(v − μ₀)` | eq. (2) | eq. (1) | **eq. (1.1)** |
| Kyle's pricing rule `P(y) = μ₀ + λy` | eq. (3) | eq. (2) | **eq. (1.2)** |
| Bayes posterior mean `P(y) = ∫ v π_y(dv)` | eq. (10) | eq. (6) | §2.2 last display, untagged |
| normalised densities `p`, `n` | §4.1 | §2.2 / App. A | **§2.2 / Appendix A** |
| "`P` is a pricing rule", "`P` continuous, `P(Y) ∈ L²`" | — | Lemma 2.2 | **Lemma 2.2** |
| order-flow law clause | — | Lemma 2.1 | **Lemma 2.1** |
| headline characterisation | Theorem 1.1 | Theorem 1 | **Theorem 1.1** |

The machinery in this file is what v4's Lemma 2.2 and the converse half of
v4 Theorem 1.1 state as paper content. Full v2 ↔ v3 map:
`STATEMENT_NOTES.md` §1; v3 → v4 crosswalk:
`V4_DELTA_REPORT_2026-09-16.md` §1 (policy:
`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision D1).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace KyleUniqueness

variable {Ω : Type*} [MeasurableSpace Ω]

namespace KyleModel

variable (M : KyleModel Ω)

/-! ## The law-level data of a Kyle model -/

/-- The noise variance `σ²` as a nonnegative real. -/
def noiseVar : ℝ≥0 := ⟨M.σ ^ 2, sq_nonneg M.σ⟩

/-- The value variance `τ²` as a nonnegative real. -/
def valueVar : ℝ≥0 := ⟨M.τ ^ 2, sq_nonneg M.τ⟩

lemma noiseVar_def : M.noiseVar = ⟨M.σ ^ 2, sq_nonneg M.σ⟩ := rfl

lemma valueVar_def : M.valueVar = ⟨M.τ ^ 2, sq_nonneg M.τ⟩ := rfl

lemma noiseVar_ne_zero : M.noiseVar ≠ 0 := fun h =>
  pow_ne_zero 2 M.hσ.ne' (congrArg NNReal.toReal h)

lemma valueVar_ne_zero : M.valueVar ≠ 0 := fun h =>
  pow_ne_zero 2 M.hτ.ne' (congrArg NNReal.toReal h)

/-- The law of the asset value: `N(μ₀, τ²)` (§1). -/
noncomputable def valueLaw : Measure ℝ := gaussianReal M.μ₀ M.valueVar

/-- The law of the noise demand: `N(0, σ²)` (§1). -/
noncomputable def noiseLaw : Measure ℝ := gaussianReal 0 M.noiseVar

instance : IsProbabilityMeasure M.valueLaw := by
  unfold valueLaw; infer_instance

instance : IsProbabilityMeasure M.noiseLaw := by
  unfold noiseLaw; infer_instance

/-- `hVlaw` in terms of `valueLaw`. -/
lemma map_V : M.μ.map M.V = M.valueLaw := M.hVlaw

/-- `hUlaw` in terms of `noiseLaw`. -/
lemma map_U : M.μ.map M.U = M.noiseLaw := M.hUlaw

/-- Independence turns the joint law of `(V, U)` into the product of the
two Gaussian laws (§1: "independent V ∼ N(μ,τ²) and U ∼ N(0,σ²)"). -/
lemma map_pair : M.μ.map (fun ω => (M.V ω, M.U ω))
    = M.valueLaw.prod M.noiseLaw := by
  rw [← M.map_V, ← M.map_U]
  exact (indepFun_iff_map_prod_eq_prod_map_map M.hV.aemeasurable
    M.hU.aemeasurable).mp M.hIndep

/-- The order flow is a random variable. -/
lemma measurable_orderFlow {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (M.orderFlow φ) := (hφ.comp M.hV).add M.hU

/-- `V` is integrable (the Gaussian has a first moment). -/
lemma integrable_V : Integrable M.V M.μ := by
  have h : Integrable id (M.μ.map M.V) := by
    rw [M.map_V]; exact integrable_id_gaussianReal _ _
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id M.hV.aemeasurable).mp h

/-- `U` is integrable. -/
lemma integrable_U : Integrable M.U M.μ := by
  have h : Integrable id (M.μ.map M.U) := by
    rw [M.map_U]; exact integrable_id_gaussianReal _ _
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id M.hU.aemeasurable).mp h

/-- `E[U] = 0` (§1: the noise demand is centred). -/
lemma integral_U : ∫ ω, M.U ω ∂M.μ = 0 := by
  calc ∫ ω, M.U ω ∂M.μ
      = ∫ x, id x ∂(M.μ.map M.U) :=
        (integral_map M.hU.aemeasurable aestronglyMeasurable_id).symm
    _ = 0 := by rw [M.map_U]; exact integral_id_gaussianReal

/-! ## Flow density and flow numerator (v4 §2.2 / Appendix A, general model)

`flowPDF φ` is the Lebesgue density of the law of the order flow
`Y_φ = φ(V) + U` (the general-σ analogue of Lemma 2.1's `p`), and
`flowNum φ` is its value-weighted counterpart (the numerator `n` of the
Bayes quotient — v4 §2.2's last display, which carries no equation tag). -/

/-- `p_φ(y) = E[ϱ_σ(y − φ(V))]` — the density of the order flow. -/
noncomputable def flowPDF (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ v, gaussianPDFReal 0 M.noiseVar (y - φ v) ∂M.valueLaw

/-- `n_φ(y) = E[V·ϱ_σ(y − φ(V))]` — the value-weighted flow density. -/
noncomputable def flowNum (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ v, v * gaussianPDFReal 0 M.noiseVar (y - φ v) ∂M.valueLaw

lemma flowPDF_def (φ : ℝ → ℝ) (y : ℝ) :
    M.flowPDF φ y
      = ∫ v, gaussianPDFReal 0 M.noiseVar (y - φ v) ∂M.valueLaw := rfl

lemma flowNum_def (φ : ℝ → ℝ) (y : ℝ) :
    M.flowNum φ y
      = ∫ v, v * gaussianPDFReal 0 M.noiseVar (y - φ v) ∂M.valueLaw := rfl

lemma flowPDF_nonneg (φ : ℝ → ℝ) (y : ℝ) : 0 ≤ M.flowPDF φ y :=
  integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _

/-- The noise kernel is integrable in the value variable (it is bounded and
the value law is a probability measure). -/
lemma integrable_noisePDF_comp {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    Integrable (fun v => gaussianPDFReal 0 M.noiseVar (y - φ v))
      M.valueLaw := by
  refine Integrable.mono' (integrable_const ((√(2 * π * M.noiseVar))⁻¹))
    ((measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub hφ)).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact gaussianPDFReal_le _ _ _

/-- `v ↦ v·ϱ_σ(y − φ(v))` is integrable against the value law. -/
lemma integrable_id_mul_noisePDF_comp {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    Integrable (fun v => v * gaussianPDFReal 0 M.noiseVar (y - φ v))
      M.valueLaw := by
  refine Integrable.mono'
    (((integrable_id_gaussianReal M.μ₀ M.valueVar).abs).const_mul
      ((√(2 * π * M.noiseVar))⁻¹))
    (measurable_id.mul ((measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub hφ))).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |v| * |gaussianPDFReal 0 M.noiseVar (y - φ v)|
      ≤ |v| * (√(2 * π * M.noiseVar))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg v)
        rw [abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
        exact gaussianPDFReal_le _ _ _
    _ = (√(2 * π * M.noiseVar))⁻¹ * |id v| := mul_comm _ _

/-! ## The master lintegral bounds

Everything the Fubini arguments below need reduces to the single Tonelli
computation `∫∫ ‖v‖·ϱ_σ(y − φ(v)) dy ν(dv) = E|V| < ∞` and its swapped
version. -/

/-- `E|V| < ∞` in lintegral form. -/
lemma lintegral_enorm_id_valueLaw_lt_top : ∫⁻ v, ‖v‖ₑ ∂M.valueLaw < ∞ :=
  (integrable_id_gaussianReal M.μ₀ M.valueVar).2

/-- Tonelli master identity: `∫∫ ‖v‖·ϱ_σ(y − φv) dy dν = ∫ ‖v‖ dν`
(the inner kernel mass is `1`). -/
lemma lintegral_lintegral_enorm_mul_kernel (φ : ℝ → ℝ) :
    ∫⁻ v, ∫⁻ y, ‖v‖ₑ *
        ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v))
        ∂volume ∂M.valueLaw
      = ∫⁻ v, ‖v‖ₑ ∂M.valueLaw := by
  refine lintegral_congr fun v => ?_
  have hm : Measurable fun y : ℝ =>
      ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v)) :=
    ((measurable_gaussianPDFReal _ _).comp
      (measurable_id.sub_const (φ v))).ennreal_ofReal
  rw [lintegral_const_mul _ hm,
    lintegral_ofReal_gaussianPDFReal_sub M.noiseVar_ne_zero (φ v), mul_one]

/-- The core domination: the `Q`-weighted kernel mass is bounded by `E|V|`,
GIVEN the density identity `Q·p_φ = n_φ`. This is where the bridge
hypothesis does its work: `|Q(y)|·p_φ(y) = |n_φ(y)| ≤ E[|V|·ϱ_σ(y − φV)]`. -/
lemma lintegral_enorm_Q_mul_kernel_le {φ Q : ℝ → ℝ} (hφ : Measurable φ)
    (heq : ∀ y, Q y * M.flowPDF φ y = M.flowNum φ y) :
    ∫⁻ y, ∫⁻ v, ‖Q y‖ₑ * ENNReal.ofReal
        (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw ∂volume
      ≤ ∫⁻ v, ‖v‖ₑ ∂M.valueLaw := by
  have hker : ∀ y : ℝ, Measurable fun v : ℝ =>
      ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v)) := fun y =>
    ((measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub hφ)).ennreal_ofReal
  -- Step 1: pointwise in `y`, the inner integral is `‖n_φ(y)‖ₑ`, which is
  -- bounded by the value-weighted kernel mass.
  have hstep : ∀ y,
      ∫⁻ v, ‖Q y‖ₑ * ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw
        ≤ ∫⁻ v, ‖v‖ₑ * ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw := by
    intro y
    rw [lintegral_const_mul _ (hker y)]
    have hp : ∫⁻ v, ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v))
        ∂M.valueLaw = ENNReal.ofReal (M.flowPDF φ y) :=
      (ofReal_integral_eq_lintegral_ofReal (M.integrable_noisePDF_comp hφ y)
        (ae_of_all _ fun v => gaussianPDFReal_nonneg _ _ _)).symm
    rw [hp]
    -- `‖Q y‖ₑ · ofReal(p) = ofReal |Q y · p| = ofReal |n(y)| = ‖n(y)‖ₑ`
    have h2 : ‖Q y‖ₑ * ENNReal.ofReal (M.flowPDF φ y)
        = ‖M.flowNum φ y‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      nth_rewrite 1 [← abs_of_nonneg (M.flowPDF_nonneg φ y)]
      rw [← abs_mul, heq y, ← Real.enorm_eq_ofReal_abs]
    rw [h2, flowNum_def]
    -- `‖∫ v·ϱ dν‖ₑ ≤ ∫⁻ ‖v·ϱ‖ₑ dν`, and `‖v·ϱ‖ₑ = ‖v‖ₑ·ofReal ϱ`
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    refine lintegral_congr fun v => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal (gaussianPDFReal_nonneg _ _ _)]
  -- Step 2: integrate the pointwise bound and swap the integration order.
  refine le_trans (lintegral_mono hstep) (le_of_eq ?_)
  have hswap : ∫⁻ y, ∫⁻ v, ‖v‖ₑ * ENNReal.ofReal
      (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw ∂volume
      = ∫⁻ v, ∫⁻ y, ‖v‖ₑ * ENNReal.ofReal
        (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂volume ∂M.valueLaw := by
    refine (lintegral_lintegral_swap ?_).symm
    exact (measurable_fst.enorm.mul (((measurable_gaussianPDFReal _ _).comp
      (measurable_snd.sub (hφ.comp measurable_fst))).ennreal_ofReal)).aemeasurable
  rw [hswap, M.lintegral_lintegral_enorm_mul_kernel φ]

/-! ## Integrability of the transferred integrands -/

/-- `z ↦ z₁·ϱ_σ(z₂ − φ z₁)` is integrable on `ν ⊗ Leb`. -/
lemma integrable_fst_mul_kernel {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Integrable (fun z : ℝ × ℝ =>
      z.1 * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1))
      (M.valueLaw.prod volume) := by
  have hmeas : Measurable fun z : ℝ × ℝ =>
      z.1 * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) :=
    measurable_fst.mul ((measurable_gaussianPDFReal _ _).comp
      (measurable_snd.sub (hφ.comp measurable_fst)))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  calc ∫⁻ z, ‖z.1 * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1)‖ₑ
        ∂(M.valueLaw.prod volume)
      = ∫⁻ v, ∫⁻ y, ‖v‖ₑ * ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂volume ∂M.valueLaw := by
        rw [lintegral_prod _ hmeas.enorm.aemeasurable]
        refine lintegral_congr fun v => lintegral_congr fun y => ?_
        rw [enorm_mul, Real.enorm_eq_ofReal (gaussianPDFReal_nonneg _ _ _)]
    _ = ∫⁻ v, ‖v‖ₑ ∂M.valueLaw := M.lintegral_lintegral_enorm_mul_kernel φ
    _ < ∞ := M.lintegral_enorm_id_valueLaw_lt_top

/-- `z ↦ Q z₂·ϱ_σ(z₂ − φ z₁)` is integrable on `ν ⊗ Leb`, given the density
identity. -/
lemma integrable_Q_mul_kernel {φ Q : ℝ → ℝ} (hφ : Measurable φ)
    (hQ : Measurable Q)
    (heq : ∀ y, Q y * M.flowPDF φ y = M.flowNum φ y) :
    Integrable (fun z : ℝ × ℝ =>
      Q z.2 * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1))
      (M.valueLaw.prod volume) := by
  have hmeas : Measurable fun z : ℝ × ℝ =>
      Q z.2 * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) :=
    (hQ.comp measurable_snd).mul ((measurable_gaussianPDFReal _ _).comp
      (measurable_snd.sub (hφ.comp measurable_fst)))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  calc ∫⁻ z, ‖Q z.2 * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1)‖ₑ
        ∂(M.valueLaw.prod volume)
      = ∫⁻ y, ∫⁻ v, ‖Q y‖ₑ * ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw ∂volume := by
        rw [lintegral_prod_symm _ hmeas.enorm.aemeasurable]
        refine lintegral_congr fun y => lintegral_congr fun v => ?_
        rw [enorm_mul, Real.enorm_eq_ofReal (gaussianPDFReal_nonneg _ _ _)]
    _ ≤ ∫⁻ v, ‖v‖ₑ ∂M.valueLaw :=
        M.lintegral_enorm_Q_mul_kernel_le hφ heq
    _ < ∞ := M.lintegral_enorm_id_valueLaw_lt_top

/-- `z ↦ Q(φ z₁ + z₂)` is integrable on `ν ⊗ ρ` (change of variables to the
kernel form, then the master bound). -/
lemma integrable_Q_comp_add {φ Q : ℝ → ℝ} (hφ : Measurable φ)
    (hQ : Measurable Q)
    (heq : ∀ y, Q y * M.flowPDF φ y = M.flowNum φ y) :
    Integrable (fun z : ℝ × ℝ => Q (φ z.1 + z.2))
      (M.valueLaw.prod M.noiseLaw) := by
  have hmeas : Measurable fun z : ℝ × ℝ => Q (φ z.1 + z.2) :=
    hQ.comp ((hφ.comp measurable_fst).add measurable_snd)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  calc ∫⁻ z, ‖Q (φ z.1 + z.2)‖ₑ ∂(M.valueLaw.prod M.noiseLaw)
      = ∫⁻ v, ∫⁻ u, ‖Q (φ v + u)‖ₑ ∂M.noiseLaw ∂M.valueLaw :=
        lintegral_prod _ hmeas.enorm.aemeasurable
    _ = ∫⁻ v, ∫⁻ y, ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) * ‖Q y‖ₑ
          ∂volume ∂M.valueLaw := by
        refine lintegral_congr fun v => ?_
        exact lintegral_comp_add_gaussianReal' M.noiseVar_ne_zero (φ v)
          hQ.enorm
    _ = ∫⁻ y, ∫⁻ v, ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) * ‖Q y‖ₑ
          ∂M.valueLaw ∂volume := by
        refine lintegral_lintegral_swap ?_
        exact ((((measurable_gaussianPDFReal _ _).comp
          (measurable_snd.sub (hφ.comp measurable_fst))).ennreal_ofReal).mul
          ((hQ.comp measurable_snd).enorm)).aemeasurable
    _ = ∫⁻ y, ∫⁻ v, ‖Q y‖ₑ * ENNReal.ofReal
          (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw ∂volume :=
        lintegral_congr fun y => lintegral_congr fun v => mul_comm _ _
    _ ≤ ∫⁻ v, ‖v‖ₑ ∂M.valueLaw :=
        M.lintegral_enorm_Q_mul_kernel_le hφ heq
    _ < ∞ := M.lintegral_enorm_id_valueLaw_lt_top

/-- `z ↦ z₁` is integrable on `ν ⊗ ρ`. -/
lemma integrable_fst_prod :
    Integrable (fun z : ℝ × ℝ => z.1) (M.valueLaw.prod M.noiseLaw) := by
  have h : Integrable id ((M.valueLaw.prod M.noiseLaw).map Prod.fst) := by
    rw [measurePreserving_fst.map_eq]
    exact integrable_id_gaussianReal _ _
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id
      measurable_fst.aemeasurable).mp h

/-! ## The master identity -/

/-- **Master identity** (the computational heart of the bridge): for any
`|g| ≤ 1` Borel test function and any Borel `Q` satisfying the density
identity `Q·p_φ = n_φ`,

`E[g(Y_φ)·Q(Y_φ)] = E[g(Y_φ)·V]`  (both sides finite).

Proof: push to the product space `(V,U) ∼ ν ⊗ ρ` (independence, §1),
integrate out the noise coordinate by the translation
`u ↦ y = φ(v) + u`, swap the order of integration (Fubini, justified by the
master bounds above), and observe that both inner value-integrals reduce to
`g(y)·n_φ(y)` — one via the density identity, one by definition. -/
theorem integral_mul_orderFlow_eq {φ Q : ℝ → ℝ} (hφ : Measurable φ)
    (hQ : Measurable Q)
    (heq : ∀ y, Q y * M.flowPDF φ y = M.flowNum φ y)
    {g : ℝ → ℝ} (hg : Measurable g) (hgb : ∀ y, |g y| ≤ 1) :
    ∫ ω, g (M.orderFlow φ ω) * Q (M.orderFlow φ ω) ∂M.μ
      = ∫ ω, g (M.orderFlow φ ω) * M.V ω ∂M.μ := by
  have hpair : AEMeasurable (fun ω => (M.V ω, M.U ω)) M.μ :=
    (M.hV.prodMk M.hU).aemeasurable
  have hkermeas : Measurable fun z : ℝ × ℝ =>
      gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) :=
    (measurable_gaussianPDFReal _ _).comp
      (measurable_snd.sub (hφ.comp measurable_fst))
  have hmeasL : Measurable fun z : ℝ × ℝ =>
      g (φ z.1 + z.2) * Q (φ z.1 + z.2) :=
    (hg.comp ((hφ.comp measurable_fst).add measurable_snd)).mul
      (hQ.comp ((hφ.comp measurable_fst).add measurable_snd))
  have hmeasR : Measurable fun z : ℝ × ℝ => g (φ z.1 + z.2) * z.1 :=
    (hg.comp ((hφ.comp measurable_fst).add measurable_snd)).mul
      measurable_fst
  -- integrability on `ν ⊗ ρ` (domination by `|Q∘T|` resp. `|z₁|`)
  have hQT : Integrable (fun z : ℝ × ℝ => Q (φ z.1 + z.2))
      (M.valueLaw.prod M.noiseLaw) := M.integrable_Q_comp_add hφ hQ heq
  have hint1 : Integrable
      (fun z : ℝ × ℝ => g (φ z.1 + z.2) * Q (φ z.1 + z.2))
      (M.valueLaw.prod M.noiseLaw) := by
    refine hQT.abs.mono' hmeasL.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hgb _)
  have hint2 : Integrable (fun z : ℝ × ℝ => g (φ z.1 + z.2) * z.1)
      (M.valueLaw.prod M.noiseLaw) := by
    refine M.integrable_fst_prod.abs.mono' hmeasR.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hgb _)
  -- Fubini integrands after the translation step
  have hswap1 : Integrable
      (Function.uncurry fun v y : ℝ =>
        gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * Q y))
      (M.valueLaw.prod volume) := by
    refine (M.integrable_Q_mul_kernel hφ hQ heq).abs.mono'
      (hkermeas.mul
        ((hg.comp measurable_snd).mul (hQ.comp measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    dsimp only [Function.uncurry]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    calc gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) * (|g z.2| * |Q z.2|)
        ≤ gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) * |Q z.2| :=
          mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_left (abs_nonneg _) (hgb _))
            (gaussianPDFReal_nonneg _ _ _)
      _ = |Q z.2| * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) :=
          mul_comm _ _
  have hswap2 : Integrable
      (Function.uncurry fun v y : ℝ =>
        gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * v))
      (M.valueLaw.prod volume) := by
    refine (M.integrable_fst_mul_kernel hφ).abs.mono'
      (hkermeas.mul
        ((hg.comp measurable_snd).mul measurable_fst)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    dsimp only [Function.uncurry]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    calc gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) * (|g z.2| * |z.1|)
        ≤ gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) * |z.1| :=
          mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_left (abs_nonneg _) (hgb _))
            (gaussianPDFReal_nonneg _ _ _)
      _ = |z.1| * gaussianPDFReal 0 M.noiseVar (z.2 - φ z.1) := mul_comm _ _
  -- the two product-space integrals both equal `∫ g·n_φ dy`
  have hL : ∫ z, g (φ z.1 + z.2) * Q (φ z.1 + z.2)
        ∂(M.valueLaw.prod M.noiseLaw)
      = ∫ y, g y * M.flowNum φ y := by
    calc ∫ z, g (φ z.1 + z.2) * Q (φ z.1 + z.2)
          ∂(M.valueLaw.prod M.noiseLaw)
        = ∫ v, ∫ u, g (φ v + u) * Q (φ v + u) ∂M.noiseLaw ∂M.valueLaw :=
          integral_prod _ hint1
      _ = ∫ v, ∫ y, gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * Q y)
            ∂volume ∂M.valueLaw := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          exact integral_comp_add_gaussianReal M.noiseVar_ne_zero (φ v)
            (hg.mul hQ).aestronglyMeasurable
      _ = ∫ y, ∫ v, gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * Q y)
            ∂M.valueLaw ∂volume := integral_integral_swap hswap1
      _ = ∫ y, g y * M.flowNum φ y := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp only
          have hcomm : (fun v =>
              gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * Q y))
              = fun v => (g y * Q y) *
                gaussianPDFReal 0 M.noiseVar (y - φ v) :=
            funext fun v => mul_comm _ _
          rw [hcomm, integral_const_mul, ← M.flowPDF_def φ y, ← heq y]
          ring
  have hR : ∫ z, g (φ z.1 + z.2) * z.1 ∂(M.valueLaw.prod M.noiseLaw)
      = ∫ y, g y * M.flowNum φ y := by
    calc ∫ z, g (φ z.1 + z.2) * z.1 ∂(M.valueLaw.prod M.noiseLaw)
        = ∫ v, ∫ u, g (φ v + u) * v ∂M.noiseLaw ∂M.valueLaw :=
          integral_prod _ hint2
      _ = ∫ v, ∫ y, gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * v)
            ∂volume ∂M.valueLaw := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          exact integral_comp_add_gaussianReal M.noiseVar_ne_zero (φ v)
            (hg.mul measurable_const).aestronglyMeasurable
      _ = ∫ y, ∫ v, gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * v)
            ∂M.valueLaw ∂volume := integral_integral_swap hswap2
      _ = ∫ y, g y * M.flowNum φ y := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp only
          have hcomm : (fun v =>
              gaussianPDFReal 0 M.noiseVar (y - φ v) * (g y * v))
              = fun v => g y *
                (v * gaussianPDFReal 0 M.noiseVar (y - φ v)) :=
            funext fun v => by ring
          rw [hcomm, integral_const_mul, ← M.flowNum_def φ y]
  -- assemble: transfer both sides of the goal to the product space
  calc ∫ ω, g (M.orderFlow φ ω) * Q (M.orderFlow φ ω) ∂M.μ
      = ∫ z, g (φ z.1 + z.2) * Q (φ z.1 + z.2)
          ∂(M.valueLaw.prod M.noiseLaw) := by
        rw [← M.map_pair, integral_map hpair hmeasL.aestronglyMeasurable]
        rfl
    _ = ∫ y, g y * M.flowNum φ y := hL
    _ = ∫ z, g (φ z.1 + z.2) * z.1 ∂(M.valueLaw.prod M.noiseLaw) := hR.symm
    _ = ∫ ω, g (M.orderFlow φ ω) * M.V ω ∂M.μ := by
        rw [← M.map_pair, integral_map hpair hmeasR.aestronglyMeasurable]
        rfl

/-- `Q(Y_φ)` is integrable, given the density identity (needed for the
conditional-expectation characterisation). -/
lemma integrable_Q_comp_orderFlow {φ Q : ℝ → ℝ} (hφ : Measurable φ)
    (hQ : Measurable Q)
    (heq : ∀ y, Q y * M.flowPDF φ y = M.flowNum φ y) :
    Integrable (fun ω => Q (M.orderFlow φ ω)) M.μ := by
  have h := (integrable_map_measure
    (hQ.comp ((hφ.comp measurable_fst).add measurable_snd)).aestronglyMeasurable
    (M.hV.prodMk M.hU).aemeasurable).mp
    (by rw [M.map_pair]; exact M.integrable_Q_comp_add hφ hQ heq)
  exact h

/-! ## The bridge theorem (blueprint node P1, direct route) -/

/-- **The pricing-rule bridge.** If a Borel `Q` satisfies the density
identity `Q·p_φ = n_φ` pointwise, then `Q` is a pricing rule for `φ`:
`Q(Y_φ) = E[V ∣ σ(Y_φ)]` almost surely (v4 §1, item 2 "market
efficiency").

Proved via the uniqueness characterisation of conditional expectation:
`Q(Y_φ)` is `σ(Y_φ)`-measurable, integrable, and has the same integral as
`V` over every `σ(Y_φ)`-set (the master identity applied to indicator test
functions). -/
theorem isPricingRule_of_forall_mul_flowPDF {φ Q : ℝ → ℝ}
    (hφ : Measurable φ) (hQ : Measurable Q)
    (heq : ∀ y, Q y * M.flowPDF φ y = M.flowNum φ y) :
    M.IsPricingRule φ Q := by
  have hY : Measurable (M.orderFlow φ) := M.measurable_orderFlow hφ
  have hm : M.flowSigma φ ≤ ‹MeasurableSpace Ω› := hY.comap_le
  refine ⟨hQ, ?_⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq hm M.integrable_V
    (fun s _ _ => (M.integrable_Q_comp_orderFlow hφ hQ heq).integrableOn)
    ?_ ?_
  · -- the set-integral identity over `σ(Y_φ)`-sets
    rintro s ⟨B, hB, rfl⟩ -
    have hind1 : ∀ x : Ω,
        ((M.orderFlow φ) ⁻¹' B).indicator
            (fun ω => Q (M.orderFlow φ ω)) x
          = B.indicator (fun _ => (1 : ℝ)) (M.orderFlow φ x)
              * Q (M.orderFlow φ x) := by
      intro x
      by_cases hx : M.orderFlow φ x ∈ B
      · rw [Set.indicator_of_mem (by exact hx),
          Set.indicator_of_mem hx, one_mul]
      · rw [Set.indicator_of_notMem (by exact hx),
          Set.indicator_of_notMem hx, zero_mul]
    have hind2 : ∀ x : Ω,
        ((M.orderFlow φ) ⁻¹' B).indicator M.V x
          = B.indicator (fun _ => (1 : ℝ)) (M.orderFlow φ x) * M.V x := by
      intro x
      by_cases hx : M.orderFlow φ x ∈ B
      · rw [Set.indicator_of_mem (by exact hx),
          Set.indicator_of_mem hx, one_mul]
      · rw [Set.indicator_of_notMem (by exact hx),
          Set.indicator_of_notMem hx, zero_mul]
    calc ∫ x in (M.orderFlow φ) ⁻¹' B, Q (M.orderFlow φ x) ∂M.μ
        = ∫ x, ((M.orderFlow φ) ⁻¹' B).indicator
            (fun ω => Q (M.orderFlow φ ω)) x ∂M.μ :=
          (integral_indicator (hY hB)).symm
      _ = ∫ x, B.indicator (fun _ => (1 : ℝ)) (M.orderFlow φ x)
            * Q (M.orderFlow φ x) ∂M.μ :=
          integral_congr_ae (ae_of_all _ hind1)
      _ = ∫ x, B.indicator (fun _ => (1 : ℝ)) (M.orderFlow φ x)
            * M.V x ∂M.μ :=
          M.integral_mul_orderFlow_eq hφ hQ heq
            (measurable_const.indicator hB)
            (fun y => by
              by_cases hy : y ∈ B
              · rw [Set.indicator_of_mem hy]; norm_num
              · rw [Set.indicator_of_notMem hy]; norm_num)
      _ = ∫ x, ((M.orderFlow φ) ⁻¹' B).indicator M.V x ∂M.μ :=
          (integral_congr_ae (ae_of_all _ hind2)).symm
      _ = ∫ x in (M.orderFlow φ) ⁻¹' B, M.V x ∂M.μ :=
          integral_indicator (hY hB)
  · -- `Q(Y_φ)` is `σ(Y_φ)`-measurable
    have hYm : Measurable[M.flowSigma φ] (M.orderFlow φ) :=
      Measurable.of_comap_le le_rfl
    exact ((hQ.comp hYm).stronglyMeasurable).aestronglyMeasurable

/-! ## Eqs. (1.1)/(1.2): the affine pair and its density identity -/

lemma measurable_kyleStrategy : Measurable M.kyleStrategy := by
  unfold kyleStrategy
  fun_prop

lemma measurable_kylePricingRule : Measurable M.kylePricingRule := by
  unfold kylePricingRule
  fun_prop

/-- Kyle's strategy in centred coordinates: `φ(μ₀ + a) = (σ/τ)·a`. -/
lemma kyleStrategy_add (a : ℝ) :
    M.kyleStrategy (M.μ₀ + a) = M.σ / M.τ * a := by
  unfold kyleStrategy
  ring

/-- Change of variables `v = μ₀ + a` for value-law integrals. -/
lemma integral_valueLaw_eq_shift (F : ℝ → ℝ) (hF : Measurable F) :
    ∫ v, F v ∂M.valueLaw = ∫ a, F (M.μ₀ + a) ∂gaussianReal 0 M.valueVar := by
  have hmap : (gaussianReal 0 M.valueVar).map (M.μ₀ + ·)
      = gaussianReal M.μ₀ M.valueVar := by
    simpa using gaussianReal_map_const_add (μ := (0 : ℝ))
      (v := M.valueVar) M.μ₀
  unfold valueLaw
  rw [← hmap, integral_map (measurable_const_add M.μ₀).aemeasurable
    hF.aestronglyMeasurable]

/-- The order-flow density of the affine strategy is `N(0, 2σ²)`
(the complete-the-square computation behind eq. (1.2)). -/
lemma flowPDF_kyleStrategy (y : ℝ) :
    M.flowPDF M.kyleStrategy y
      = gaussianPDFReal 0 ⟨2 * M.σ ^ 2, by positivity⟩ y := by
  have hpost : ((⟨M.τ ^ 2 / 2, by positivity⟩ : ℝ≥0)) ≠ 0 := fun h =>
    (div_pos (pow_pos M.hτ 2) two_pos).ne' (congrArg NNReal.toReal h)
  have hF : Measurable fun v : ℝ =>
      gaussianPDFReal 0 M.noiseVar (y - M.kyleStrategy v) :=
    (measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub M.measurable_kyleStrategy)
  rw [flowPDF_def, M.integral_valueLaw_eq_shift _ hF,
    integral_gaussianReal_eq_integral_smul M.valueVar_ne_zero]
  calc ∫ a, gaussianPDFReal 0 M.valueVar a •
        gaussianPDFReal 0 M.noiseVar (y - M.kyleStrategy (M.μ₀ + a))
      = ∫ a, gaussianPDFReal 0 ⟨2 * M.σ ^ 2, by positivity⟩ y *
          gaussianPDFReal (M.τ / (2 * M.σ) * y) ⟨M.τ ^ 2 / 2, by positivity⟩
            a := by
        refine integral_congr_ae (ae_of_all _ fun a => ?_)
        dsimp only
        rw [smul_eq_mul, M.kyleStrategy_add a, mul_comm, M.noiseVar_def,
          M.valueVar_def,
          gaussianPDFReal_mul_gaussianPDFReal_kyle M.hσ M.hτ y a]
    _ = gaussianPDFReal 0 ⟨2 * M.σ ^ 2, by positivity⟩ y := by
        rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hpost,
          mul_one]

/-- The value-weighted order-flow density of the affine strategy:
`n(y) = ϱ_{2σ²}(y)·(μ₀ + λy)` with `λ = τ/(2σ)` — the posterior mean is
Kyle's price (eq. (1.2)). -/
lemma flowNum_kyleStrategy (y : ℝ) :
    M.flowNum M.kyleStrategy y
      = gaussianPDFReal 0 ⟨2 * M.σ ^ 2, by positivity⟩ y
          * (M.μ₀ + M.τ / (2 * M.σ) * y) := by
  have hpost : ((⟨M.τ ^ 2 / 2, by positivity⟩ : ℝ≥0)) ≠ 0 := fun h =>
    (div_pos (pow_pos M.hτ 2) two_pos).ne' (congrArg NNReal.toReal h)
  have hF : Measurable fun v : ℝ =>
      v * gaussianPDFReal 0 M.noiseVar (y - M.kyleStrategy v) :=
    measurable_id.mul ((measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub M.measurable_kyleStrategy))
  rw [flowNum_def, M.integral_valueLaw_eq_shift _ hF,
    integral_gaussianReal_eq_integral_smul M.valueVar_ne_zero]
  calc ∫ a, gaussianPDFReal 0 M.valueVar a •
        ((M.μ₀ + a) *
          gaussianPDFReal 0 M.noiseVar (y - M.kyleStrategy (M.μ₀ + a)))
      = ∫ a, gaussianPDFReal 0 ⟨2 * M.σ ^ 2, by positivity⟩ y *
          ((M.μ₀ + a) * gaussianPDFReal (M.τ / (2 * M.σ) * y)
            ⟨M.τ ^ 2 / 2, by positivity⟩ a) := by
        refine integral_congr_ae (ae_of_all _ fun a => ?_)
        dsimp only
        rw [smul_eq_mul, M.kyleStrategy_add a]
        rw [show gaussianPDFReal 0 M.valueVar a *
            ((M.μ₀ + a) * gaussianPDFReal 0 M.noiseVar (y - M.σ / M.τ * a))
            = (M.μ₀ + a) * (gaussianPDFReal 0 M.noiseVar (y - M.σ / M.τ * a)
              * gaussianPDFReal 0 M.valueVar a) from by ring,
          M.noiseVar_def, M.valueVar_def,
          gaussianPDFReal_mul_gaussianPDFReal_kyle M.hσ M.hτ y a]
        ring
    _ = gaussianPDFReal 0 ⟨2 * M.σ ^ 2, by positivity⟩ y
          * (M.μ₀ + M.τ / (2 * M.σ) * y) := by
        rw [integral_const_mul]
        congr 1
        have hexpand : (fun a => (M.μ₀ + a) *
            gaussianPDFReal (M.τ / (2 * M.σ) * y)
              ⟨M.τ ^ 2 / 2, by positivity⟩ a)
            = fun a => M.μ₀ * gaussianPDFReal (M.τ / (2 * M.σ) * y)
                ⟨M.τ ^ 2 / 2, by positivity⟩ a
              + a * gaussianPDFReal (M.τ / (2 * M.σ) * y)
                ⟨M.τ ^ 2 / 2, by positivity⟩ a :=
          funext fun a => by ring
        rw [hexpand, integral_add
          ((integrable_gaussianPDFReal _ _).const_mul M.μ₀)
          (integrable_id_mul_gaussianPDFReal _ _),
          integral_const_mul, integral_gaussianPDFReal_eq_one _ hpost,
          integral_id_mul_gaussianPDFReal _ hpost, mul_one]

/-- **Eq. (1.2)'s density identity**: the affine rule `P(y) = μ₀ + λy`
satisfies `P·p = n` for the affine strategy. -/
lemma kylePricingRule_mul_flowPDF (y : ℝ) :
    M.kylePricingRule y * M.flowPDF M.kyleStrategy y
      = M.flowNum M.kyleStrategy y := by
  rw [M.flowPDF_kyleStrategy y, M.flowNum_kyleStrategy y]
  unfold kylePricingRule priceImpact
  ring

/-! ## v4 §1's profit against the affine rule: the profit quadratic -/

/-- Against the affine pricing rule, the insider's expected profit
(v4 §1, item 1) is the deterministic quadratic `(v − μ₀ − λx)·x`
(`E[U] = 0` kills the noise term). -/
lemma expectedProfit_kylePricingRule (v x : ℝ) :
    M.expectedProfit M.kylePricingRule v x
      = (v - M.μ₀ - M.priceImpact * x) * x := by
  unfold expectedProfit kylePricingRule
  have hrw : (fun ω => (v - (M.μ₀ + M.priceImpact * (x + M.U ω))) * x)
      = fun ω => (v - M.μ₀ - M.priceImpact * x) * x
          - M.priceImpact * x * M.U ω :=
    funext fun ω => by ring
  rw [hrw, integral_sub (integrable_const _)
    (M.integrable_U.const_mul _), integral_const, integral_const_mul,
    M.integral_U, mul_zero, sub_zero]
  simp

/-- The profit quadratic is maximised at Kyle's strategy
`x* = (σ/τ)(v − μ₀)` (eq. (1.1)): the pointwise optimality of v4 §1,
item 1. -/
lemma expectedProfit_kylePricingRule_le (v x : ℝ) :
    M.expectedProfit M.kylePricingRule v x
      ≤ M.expectedProfit M.kylePricingRule v (M.kyleStrategy v) := by
  rw [M.expectedProfit_kylePricingRule, M.expectedProfit_kylePricingRule]
  have hσ' : M.σ ≠ 0 := M.hσ.ne'
  have hτ' : M.τ ≠ 0 := M.hτ.ne'
  rw [← sub_nonneg]
  have hexp : (v - M.μ₀ - M.priceImpact * M.kyleStrategy v)
        * M.kyleStrategy v
      - (v - M.μ₀ - M.priceImpact * x) * x
      = M.priceImpact * (x - M.kyleStrategy v) ^ 2 := by
    unfold kyleStrategy priceImpact
    field_simp
    ring
  rw [hexp]
  have hlam : 0 < M.priceImpact := div_pos M.hτ (mul_pos two_pos M.hσ)
  exact mul_nonneg hlam.le (sq_nonneg _)

/-! ## The law of the order flow (v4 Lemma 2.1's law clause, general σ)

The law of `Y_φ = φ(V) + U` is the `flowPDF`-weighted Lebesgue measure —
proved by pushing to the product space, translating the noise coordinate
(`lintegral_comp_add_gaussianReal'`), and one Tonelli swap. Consumed by the
pricing half of Theorem 1.1's uniqueness (flow-a.s. ⇒ Lebesgue-a.e., since
`flowPDF > 0`). -/

/-- The flow density is Borel measurable (parametric-integral
measurability). -/
lemma measurable_flowPDF {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (M.flowPDF φ) := by
  have h : StronglyMeasurable fun p : ℝ × ℝ =>
      gaussianPDFReal 0 M.noiseVar (p.1 - φ p.2) :=
    ((measurable_gaussianPDFReal _ _).comp
      (measurable_fst.sub (hφ.comp measurable_snd))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- The `ℝ≥0∞`-valued kernel mass at `y` is the flow density at `y`. -/
lemma lintegral_ofReal_kernel_eq_flowPDF {φ : ℝ → ℝ} (hφ : Measurable φ)
    (y : ℝ) :
    ∫⁻ v, ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v)) ∂M.valueLaw
      = ENNReal.ofReal (M.flowPDF φ y) :=
  (ofReal_integral_eq_lintegral_ofReal (M.integrable_noisePDF_comp hφ y)
    (ae_of_all _ fun _ => gaussianPDFReal_nonneg _ _ _)).symm

/-- **The order-flow law identity**: the law of `Y_φ = φ(V) + U` is the
`flowPDF`-weighted Lebesgue measure. -/
lemma map_orderFlow {φ : ℝ → ℝ} (hφ : Measurable φ) :
    M.μ.map (M.orderFlow φ)
      = (volume : Measure ℝ).withDensity
          (fun y => ENNReal.ofReal (M.flowPDF φ y)) := by
  have hg : Measurable fun z : ℝ × ℝ => φ z.1 + z.2 :=
    (hφ.comp measurable_fst).add measurable_snd
  refine Measure.ext fun s hs => ?_
  have hmap : M.μ.map (M.orderFlow φ)
      = (M.valueLaw.prod M.noiseLaw).map fun z : ℝ × ℝ => φ z.1 + z.2 := by
    rw [← M.map_pair, Measure.map_map hg (M.hV.prodMk M.hU)]
    rfl
  rw [hmap, Measure.map_apply hg hs, Measure.prod_apply (hg hs),
    withDensity_apply _ hs]
  calc ∫⁻ v, M.noiseLaw
        (Prod.mk v ⁻¹' ((fun z : ℝ × ℝ => φ z.1 + z.2) ⁻¹' s)) ∂M.valueLaw
      = ∫⁻ v, ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v))
          * s.indicator 1 y ∂volume ∂M.valueLaw := by
        refine lintegral_congr fun v => ?_
        have hpre : Prod.mk v ⁻¹' ((fun z : ℝ × ℝ => φ z.1 + z.2) ⁻¹' s)
            = (fun u => φ v + u) ⁻¹' s := rfl
        have hind : ∀ u : ℝ,
            ((fun u => φ v + u) ⁻¹' s).indicator (1 : ℝ → ℝ≥0∞) u
              = s.indicator 1 (φ v + u) := by
          intro u
          by_cases h : φ v + u ∈ s
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by exact h)]
            rfl
          · rw [Set.indicator_of_notMem h,
              Set.indicator_of_notMem (by exact h)]
        rw [hpre, ← lintegral_indicator_one (measurable_const_add (φ v) hs)]
        rw [lintegral_congr hind]
        exact lintegral_comp_add_gaussianReal' M.noiseVar_ne_zero (φ v)
          (measurable_one.indicator hs)
    _ = ∫⁻ y, ∫⁻ v, ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v))
          * s.indicator 1 y ∂M.valueLaw ∂volume := by
        refine lintegral_lintegral_swap ?_
        exact ((((measurable_gaussianPDFReal _ _).comp
          (measurable_snd.sub (hφ.comp measurable_fst))).ennreal_ofReal).mul
          ((measurable_one.indicator hs).comp measurable_snd)).aemeasurable
    _ = ∫⁻ y in s, ENNReal.ofReal (M.flowPDF φ y) ∂volume := by
        rw [← lintegral_indicator hs]
        refine lintegral_congr fun y => ?_
        have hmeas : Measurable fun v : ℝ =>
            ENNReal.ofReal (gaussianPDFReal 0 M.noiseVar (y - φ v)) :=
          ((measurable_gaussianPDFReal _ _).comp
            (measurable_const.sub hφ)).ennreal_ofReal
        rw [lintegral_mul_const _ hmeas,
          M.lintegral_ofReal_kernel_eq_flowPDF hφ y]
        by_cases hy : y ∈ s
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
            Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
            mul_zero]

/-- Flow-a.s. agreement of pricing rules transfers to Lebesgue-a.e.
agreement whenever the flow density is everywhere positive. -/
lemma pricingRule_ae_eq_of_flowPDF_pos {φ P Q : ℝ → ℝ} (hφ : Measurable φ)
    (hP : M.IsPricingRule φ P) (hQ : M.IsPricingRule φ Q)
    (hpos : ∀ y, 0 < M.flowPDF φ y) :
    P =ᵐ[(volume : Measure ℝ)] Q := by
  have hY : Measurable (M.orderFlow φ) := M.measurable_orderFlow hφ
  -- the two rules agree a.s. along the flow (both are versions of E[V∣Y])
  have hflow : (fun ω => P (M.orderFlow φ ω)) =ᵐ[M.μ]
      fun ω => Q (M.orderFlow φ ω) :=
    hP.ae_eq_condExp.trans hQ.ae_eq_condExp.symm
  -- as an a.e. statement for the law of the flow
  have hset : MeasurableSet {y : ℝ | P y = Q y} :=
    measurableSet_eq_fun hP.measurable hQ.measurable
  have hmapae : ∀ᵐ y ∂(M.μ.map (M.orderFlow φ)), P y = Q y :=
    (ae_map_iff hY.aemeasurable hset).mpr hflow
  -- transfer through the withDensity structure of the law
  rw [M.map_orderFlow hφ] at hmapae
  have h := (ae_withDensity_iff'
    (M.measurable_flowPDF hφ).ennreal_ofReal.aemeasurable).mp hmapae
  filter_upwards [h] with y hy
  exact hy (ENNReal.ofReal_pos.mpr (hpos y)).ne'

end KyleModel

/-! ## The normalised model: bridging to §2's explicit objects -/

@[simp] lemma stdModel_μ₀ : stdModel.μ₀ = 0 := rfl

@[simp] lemma stdModel_τ : stdModel.τ = 1 := rfl

@[simp] lemma stdModel_σ : stdModel.σ = 1 := rfl

lemma stdModel_noiseVar : stdModel.noiseVar = 1 := by
  rw [show stdModel.noiseVar = ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ from rfl]
  exact Subtype.ext (one_pow 2)

lemma stdModel_valueVar : stdModel.valueVar = 1 := by
  rw [show stdModel.valueVar = ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ from rfl]
  exact Subtype.ext (one_pow 2)

lemma stdModel_valueLaw : stdModel.valueLaw = gaussianReal 0 1 := by
  rw [KyleModel.valueLaw, stdModel_valueVar, stdModel_μ₀]

lemma stdModel_noiseLaw : stdModel.noiseLaw = gaussianReal 0 1 := by
  rw [KyleModel.noiseLaw, stdModel_noiseVar]

/-- On the normalised model the general flow density is §2's `p`
(`flowDensity` of `Definitions.lean`). -/
lemma stdModel_flowPDF (φ : ℝ → ℝ) (y : ℝ) :
    stdModel.flowPDF φ y = flowDensity φ y := by
  rw [KyleModel.flowPDF_def, stdModel_valueLaw, stdModel_noiseVar,
    flowDensity, stdNormalPDF]

/-- On the normalised model the general flow numerator is §2's `n` — the
numerator of the Bayes quotient defining `inverseRegression` (v4 §2.2's
last display). -/
lemma stdModel_flowNum (φ : ℝ → ℝ) (y : ℝ) :
    stdModel.flowNum φ y
      = ∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1 := by
  rw [KyleModel.flowNum_def, stdModel_valueLaw, stdModel_noiseVar,
    stdNormalPDF]

/-- The explicit inverse regression (v4 §2.2's last display) is Borel
measurable
(parametric-integral measurability for numerator and denominator). -/
lemma measurable_inverseRegression {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (inverseRegression φ) := by
  have hnum : StronglyMeasurable fun p : ℝ × ℝ =>
      p.2 * stdNormalPDF (p.1 - φ p.2) :=
    (measurable_snd.mul ((measurable_gaussianPDFReal 0 1).comp
      (measurable_fst.sub (hφ.comp measurable_snd)))).stronglyMeasurable
  have hden : StronglyMeasurable fun p : ℝ × ℝ =>
      stdNormalPDF (p.1 - φ p.2) :=
    ((measurable_gaussianPDFReal 0 1).comp
      (measurable_fst.sub (hφ.comp measurable_snd))).stronglyMeasurable
  unfold inverseRegression flowDensity
  exact (hnum.integral_prod_right'.measurable).div
    (hden.integral_prod_right'.measurable)

end KyleUniqueness
