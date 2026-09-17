/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Accounting
import KyleUniqueness.SignedRoot

/-!
# Main theorems (v4 Theorem 7.1 rigidity, Prop 6.1 saturation, Theorem 1.1 uniqueness)

The top of the import DAG for the formalization of Monteiro & Tourky, *The
one-period Kyle model has one equilibrium*
(arXiv:2607.23585, **v4** of 2026-08-20). Everything below this file is
either a definition, a lemma of §2–§6, or one of the two halves of the
headline that do not need the §4–§6 machinery; this file assembles them.

Numbering in this file is v4's (`blueprint/LANE_C_DECISIONS_2026-09-16.md`,
decision D1). The whole Lean tree — `KyleUniqueness.Statement` and the other
v3-session modules included — was re-keyed to v4 in the closeout wave, so
the six declarations *moved here from* `KyleUniqueness.Statement` now carry
v4 numbers too; `STATEMENT_NOTES.md` still catalogues them under v3 numbers.
The crosswalk is: v3 Theorem 3 = **v4 Prop 6.1**, v3 Theorem 4 = **v4
Theorem 7.1**, v3 Theorem 1 = **v4 Theorem 1.1**, v3 Proposition 2 = **v4
Prop 4.1**; the full map is `V4_DELTA_REPORT_2026-09-16.md` §1.

## Main results

* `gamma_eq_half` — **v4 Proposition 6.1** on the normalised model: every
  `φ` satisfying the pointwise maximisation condition has `Γ = 1/2`. The
  two halves are `one_le_two_mul_noiseTraderLoss` (node J1, `1 ≤ 2Γ`, from
  the signed root plus the one-sided Stein inequality) and
  `noiseTraderLoss_le_half` (v4 Prop 4.1, `|Γ| ≤ 1/2`).
* `monotone_eq_of_ae_eq_continuous` — the rigidity upgrade from
  Lebesgue-a.e. to everywhere for a monotone function.
* `isGammaSolution_zero_iff` / `existsUnique_zeroSolution` — **v4 Theorem
  7.1** (v3 Theorem 4): the pointwise maximisation condition (17) holds iff
  `φ = id`, and `id` is the unique such strategy.
* `KyleModel.stdStrategy`, `KyleModel.bayesPrice` and the
  `*_mul_sigma` family — the location–scale standardisation of **v4 §7**
  ("translation and rescaling of the rigidity theorem"), blueprint node O1.
* `isEquilibrium_eq_kyleStrategy`, `kyle_unique_equilibrium`,
  `kyle_existsUnique_equilibrium`, `kyle_equilibrium_pair_iff` — **v4
  Theorem 1.1** (v3 Theorem 1), the headline, in its strategy, `∃!` and
  pair forms.

## Proof-debt surface

**None.** With node O1 (`isEquilibrium_eq_kyleStrategy`, the location–scale
standardisation of v4 §7) closed, the development has **no open
obligations**: every declaration in every module is `sorry`-free and
depends only on `[propext, Classical.choice, Quot.sound]`
(machine-checked at every build by `KyleUniqueness.AxiomAudit`).
-/

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology

namespace KyleUniqueness

/-! ## v4 Proposition 6.1: the saturation `Γ = 1/2` (blueprint node T3) -/

/-- **v4 Proposition 6.1** (v3 Theorem 3) on the normalised model: if `φ`
satisfies the pointwise maximisation condition (17) then the noise traders'
expected loss is exactly `Γ = 1/2`.

Both halves of the paper's sandwich are already banked: `1 ≤ 2Γ` is node J1
(`one_le_two_mul_noiseTraderLoss`, the signed-root construction fed to the
one-sided Stein inequality), whose two hypotheses are the conclusions of v4
Proposition 5.1 (`integrable_insiderProfit_of_isGammaSolution` and
`noiseTraderLoss_eq_integral_insiderProfit`), and `Γ ≤ 1/2` is the upper
half of v4 Proposition 4.1 (`noiseTraderLoss_le_half`, which needs nothing
beyond Borel measurability). -/
theorem gamma_eq_half {φ : ℝ → ℝ} (h : IsGammaSolution 0 φ) :
    noiseTraderLoss φ = 1 / 2 := by
  have hlo : 1 ≤ 2 * noiseTraderLoss φ :=
    one_le_two_mul_noiseTraderLoss h (integrable_insiderProfit_of_isGammaSolution h)
      (noiseTraderLoss_eq_integral_insiderProfit h)
  have hup : noiseTraderLoss φ ≤ 1 / 2 := (abs_le.1 (noiseTraderLoss_le_half h.1)).2
  linarith

/-! ## From Lebesgue-a.e. equality to equality -/

/-- A monotone function that agrees Lebesgue-almost everywhere with a
continuous function agrees with it **everywhere**.

This is the bridge v4 Theorem 7.1 needs: v4 Proposition 4.1's equality case
only delivers `φ = (· + a)` off a Lebesgue-null set, while the pointwise
maximisation condition is a statement at *every* `v`. The proof is the
standard density squeeze: the agreement set has null complement, so it
meets every nonempty open interval (`Real.volume_Ioo` is positive), and
monotonicity sandwiches `φ v` between values of `g` at agreement points on
either side of `v`, which converge to `g v` by continuity. -/
theorem monotone_eq_of_ae_eq_continuous {φ g : ℝ → ℝ} (hmono : Monotone φ)
    (hg : Continuous g) (hae : φ =ᵐ[(volume : Measure ℝ)] g) : φ = g := by
  -- The disagreement set is Lebesgue-null, so every nonempty open interval
  -- contains a point of agreement.
  have hnull : (volume : Measure ℝ) {x : ℝ | ¬ φ x = g x} = 0 := ae_iff.1 hae
  have hmeet : ∀ a b : ℝ, a < b → ∃ x ∈ Ioo a b, φ x = g x := by
    intro a b hab
    by_contra hcon
    have hsub : Ioo a b ⊆ {x : ℝ | ¬ φ x = g x} := fun x hx hx' => hcon ⟨x, hx, hx'⟩
    have hle : (volume : Measure ℝ) (Ioo a b) = 0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hle
    linarith
  funext v
  refine le_antisymm ?_ ?_
  · -- `φ v ≤ g v`, from agreement points just to the right of `v`.
    by_contra hcon
    rw [not_le] at hcon
    have hnhds : g ⁻¹' Iio (φ v) ∈ 𝓝 v :=
      hg.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hcon)
    obtain ⟨l, u, ⟨hlv, hvu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnhds
    obtain ⟨x, hx, hxeq⟩ := hmeet v u hvu
    have hgx : g x < φ v := hsub ⟨hlv.trans hx.1, hx.2⟩
    have hmx : φ v ≤ φ x := hmono hx.1.le
    rw [hxeq] at hmx
    linarith
  · -- `g v ≤ φ v`, from agreement points just to the left of `v`.
    by_contra hcon
    rw [not_le] at hcon
    have hnhds : g ⁻¹' Ioi (φ v) ∈ 𝓝 v :=
      hg.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hcon)
    obtain ⟨l, u, ⟨hlv, hvu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnhds
    obtain ⟨x, hx, hxeq⟩ := hmeet l v hlv
    have hgx : φ v < g x := hsub ⟨hx.1, hx.2.trans hvu⟩
    have hmx : φ x ≤ φ v := hmono hx.2.le
    rw [hxeq] at hmx
    linarith

/-! ## Theorem 7.1: the pointwise-maximisation condition forces `φ = id`

v3 promoted v2's Corollary 3.3 to a main theorem; v4 numbers it **Theorem
7.1** (§7, "Rigidity"). The proof route is Proposition 6.1 (`Γ = 1/2` for
any `φ` satisfying the pointwise-maximisation condition) + Proposition 4.1's
equality case (`φ = v + a` a.e.) + the Gaussian regression for affine
strategies + the pointwise argmax comparison forcing `a = 0`. -/

/-- **v4 Theorem 7.1** (v3 Theorem 4): `φ` satisfies
`φ(v) ∈ argmax_x {x(v − F(x))}` for every `v ∈ ℝ` (the
pointwise-maximisation condition, untagged in v4; v3 tagged it (17) with
display (19)) iff `φ = id`. This is the primary rigidity statement; it
carries the proof obligation directly (v2 derived it from the deleted
general-`γ` classification). -/
theorem isGammaSolution_zero_iff (φ : ℝ → ℝ) :
    IsGammaSolution 0 φ ↔ φ = id := by
  constructor
  · -- Rigidity direction (blueprint N2, CLOSED): Theorem 3 (`Γ = 1/2`
    -- under condition (17), assembled as `gamma_eq_half` from the §4–§6
    -- machinery — value function W (B1/B2), posterior differentiation
    -- (D1/D2), conditional resampling + balance identity (E1/E2), signed
    -- root (H1), Stein pipeline (I1–I3), J1 + T3) feeds Proposition 2's
    -- equality case (`noiseTraderLoss_eq_half_iff`), which gives
    -- `φ = (· + a)` Lebesgue-a.e.; monotonicity of a pointwise maximiser
    -- upgrades that to an everywhere identity; the affine regression
    -- (`gaussianSmoothing_affine`) then makes the objective explicit and
    -- the argmax comparison at `v = 0` forces `a = 0`.
    intro h
    obtain ⟨a, ha⟩ := (noiseTraderLoss_eq_half_iff h.1).1 (gamma_eq_half h)
    have hφa : φ = fun v => v + a :=
      monotone_eq_of_ae_eq_continuous (monotone_of_isGammaSolution h)
        (by fun_prop) ha
    have ha0 : a = 0 := by
      -- Compare the objective at the admissible order `x = a/2` with its
      -- value at `x = φ 0 = a`: `a²/8 ≤ 0`.
      have hcmp := h.2 0 (a / 2)
      rw [hφa] at hcmp
      simp only [objective, gaussianSmoothing_affine] at hcmp
      have hsq : a ^ 2 ≤ 0 := by nlinarith
      exact sq_eq_zero_iff.1 (le_antisymm hsq (sq_nonneg a))
    rw [hφa, ha0]
    funext v
    simp
  · -- Existence direction: with `F(x) = x/2` (`gaussianSmoothing_id`,
    -- PROVED), the objective is the strictly concave quadratic
    -- `x(v − x/2)`, maximised at `x = v` for every `v`.
    rintro rfl
    refine ⟨measurable_id, fun v x => ?_⟩
    simp only [objective, gaussianSmoothing_id, id_eq]
    nlinarith [sq_nonneg (x - v)]

/-- v4 Theorem 7.1, `∃!`-packaging: exactly one Borel strategy satisfies
the pointwise-maximisation condition. Assembled from
`isGammaSolution_zero_iff`; no `sorry` of its own. -/
theorem existsUnique_zeroSolution : ∃! φ : ℝ → ℝ, IsGammaSolution 0 φ :=
  ⟨id, (isGammaSolution_zero_iff id).mpr rfl,
    fun ψ hψ => (isGammaSolution_zero_iff ψ).mp hψ⟩

/-! ## Theorem 1.1: the strategy layer -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Theorem 1's strategy half: the location–scale standardisation (v4 §7)

v4 closes the headline by *standardising*: with `V̂ := (V − μ₀)/τ` and
`Û := U/σ` standard normal and independent, the strategy becomes
`φ̂(t) := φ(μ₀ + τt)/σ` and the pricing rule `P̂(y) := (P(σy) − μ₀)/τ`; the
order flow rescales as `φ̂(V̂) + Û = Y_φ/σ`, market efficiency is preserved,
and expected profits are multiplied by the positive constant `στ`. By
Theorem 7.1 (`isGammaSolution_zero_iff`) the standardised strategy is the
identity, i.e. `φ(v) = (σ/τ)(v − μ₀)` — Kyle's strategy, eq. (1).

**Route taken** (chosen over building a standardised `KyleModel` on the same
`Ω`): the argument never needs the standardised *probability space*, only
the standardised *laws*, and `N(μ₀, τ²)`, `N(0, σ²)` are the push-forwards
of the standard normal under `t ↦ μ₀ + τt` and `s ↦ σs`
(`KyleModel.map_std_valueLaw`, `KyleModel.map_std_noiseLaw`). So the whole
of §7's change of variables happens inside two Bochner integrals, and the
σ-algebra/conditional-expectation transport that a second `KyleModel` would
force (a `comap` through `y ↦ y/σ`, then `condExp_sub`/`condExp_smul`) is
avoided entirely. The chain is:

* `KyleModel.flowPDF_mul_sigma` — `p_φ(σy) = p̂(y)/σ`;
* `KyleModel.flowNum_mul_sigma` — `n_φ(σy) = (μ₀ p̂(y) + τ n̂(y))/σ`;
* `KyleModel.bayesPrice_mul_sigma` — hence `P₀(σy) = μ₀ + τ·P̂(y)` for the
  canonical Bayes-quotient version `P₀ = n_φ/p_φ` of the pricing rule,
  which is §7's `P̂` read backwards, and `P̂ = inverseRegression φ̂` is §2's
  normalised object, so Theorem 7.1 applies to it verbatim;
* `KyleModel.expectedProfit_bayesPrice` — hence
  `E[(μ₀+τv − P₀(σx+U))·σx] = στ·x(v − F̂(x))`, the profit rescaling.

Version-independence closes the loop: `p_φ > 0` everywhere
(`KyleModel.flowPDF_pos`) makes any pricing rule agree with `P₀` off a
Lebesgue-null set (`pricingRule_ae_eq_of_flowPDF_pos`), and
`expectedProfit_congr_ae` transports the maximisation hypothesis from the
arbitrary version supplied by `IsEquilibriumStrategy` to `P₀`. -/

/-- Gaussian pdf under a positive rescaling: `ϱ_{s²}(s·z) = ϱ(z)/s`. The
one analytic input of the standardisation (everything else is a
push-forward identity). -/
private lemma gaussianPDFReal_mul_of_pos {s : ℝ} (hs : 0 < s) {v : NNReal}
    (hv : (v : ℝ) = s ^ 2) (z : ℝ) :
    gaussianPDFReal 0 v (s * z) = gaussianPDFReal 0 1 z / s := by
  have hs0 : s ≠ 0 := hs.ne'
  have h1 : Real.sqrt (2 * Real.pi * (v : ℝ)) = Real.sqrt (2 * Real.pi) * s := by
    rw [hv, Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
  have h2 : -(s * z - 0) ^ 2 / (2 * (v : ℝ)) = -(z - 0) ^ 2 / 2 := by
    rw [hv]
    field_simp
    ring
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one]
  rw [h1, h2]
  ring

/-- `stdNormalPDF` spelled as `gaussianPDFReal 0 1` (PROVING_LOG gotcha:
the two spellings are defeq but `rw`/`simp` do not see through the
`noncomputable def`). -/
private lemma stdNormalPDF_apply (z : ℝ) : stdNormalPDF z = gaussianPDFReal 0 1 z := rfl

/-- `u ↦ P(x + u)` is `γ`-integrable for the canonical normalised pricing
rule (v4 Lemma 2.3 in the shifted form). This is the step inlined in the
proof of `equilibrium_iff_zeroSolution`, factored out here because the
location–scale argument needs it at a general `x`. -/
private lemma integrable_inverseRegression_shift {φ : ℝ → ℝ}
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

namespace KyleModel

variable (M : KyleModel Ω)

/-- The standardised strategy `φ̂(t) := φ(μ₀ + τt)/σ` (v4 §7). -/
noncomputable def stdStrategy (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => φ (M.μ₀ + M.τ * t) / M.σ

/-- The canonical (Bayes-quotient) pricing rule `n_φ/p_φ` of a general Kyle
model — the general-`M` form of §2's `inverseRegression`, and the version
against which the standardisation is run. -/
noncomputable def bayesPrice (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  M.flowNum φ y / M.flowPDF φ y

lemma measurable_stdStrategy {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (M.stdStrategy φ) := by
  unfold stdStrategy
  fun_prop

/-- `σ·φ̂(t) = φ(μ₀ + τt)`: the defining relation, cleared of the division. -/
lemma mul_stdStrategy (φ : ℝ → ℝ) (t : ℝ) :
    M.σ * M.stdStrategy φ t = φ (M.μ₀ + M.τ * t) := by
  have hσ : M.σ ≠ 0 := M.hσ.ne'
  unfold stdStrategy
  field_simp

/-- The value law `N(μ₀, τ²)` is the push-forward of the standard normal
under the location–scale map `t ↦ μ₀ + τt`. -/
lemma map_std_valueLaw :
    (gaussianReal 0 1).map (fun t => M.μ₀ + M.τ * t) = M.valueLaw := by
  have hv : M.valueLaw = gaussianReal M.μ₀ M.valueVar := rfl
  rw [hv, show (fun t : ℝ => M.μ₀ + M.τ * t)
      = ((fun u : ℝ => M.μ₀ + u) ∘ fun t : ℝ => M.τ * t) from rfl,
    ← Measure.map_map (measurable_const_add M.μ₀) (measurable_const_mul M.τ),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  congr 1
  · ring
  · rw [mul_one]
    exact M.valueVar_def.symm

/-- The noise law `N(0, σ²)` is the push-forward of the standard normal
under the scaling `s ↦ σs`. -/
lemma map_std_noiseLaw :
    (gaussianReal 0 1).map (fun s => M.σ * s) = M.noiseLaw := by
  have hv : M.noiseLaw = gaussianReal 0 M.noiseVar := rfl
  rw [hv, gaussianReal_map_const_mul]
  congr 1
  · ring
  · rw [mul_one]
    exact M.noiseVar_def.symm

/-- Change of variables `v = μ₀ + τt` for value-law integrals. -/
lemma integral_valueLaw_std {F : ℝ → ℝ} (hF : AEStronglyMeasurable F M.valueLaw) :
    ∫ v, F v ∂M.valueLaw = ∫ t, F (M.μ₀ + M.τ * t) ∂gaussianReal 0 1 := by
  have hmap : Measurable (fun t : ℝ => M.μ₀ + M.τ * t) := by fun_prop
  conv_lhs => rw [← M.map_std_valueLaw]
  exact integral_map hmap.aemeasurable (by rwa [M.map_std_valueLaw])

/-- Change of variables `u = σs` for noise-law integrals. -/
lemma integral_noiseLaw_std {F : ℝ → ℝ} (hF : AEStronglyMeasurable F M.noiseLaw) :
    ∫ u, F u ∂M.noiseLaw = ∫ s, F (M.σ * s) ∂gaussianReal 0 1 := by
  have hmap : Measurable (fun s : ℝ => M.σ * s) := by fun_prop
  conv_lhs => rw [← M.map_std_noiseLaw]
  exact integral_map hmap.aemeasurable (by rwa [M.map_std_noiseLaw])

/-- The value-weighted flow density is Borel (parametric-integral
measurability, as for `measurable_flowPDF`). -/
lemma measurable_flowNum {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (M.flowNum φ) := by
  have h : StronglyMeasurable fun p : ℝ × ℝ =>
      p.2 * gaussianPDFReal 0 M.noiseVar (p.1 - φ p.2) :=
    (measurable_snd.mul ((measurable_gaussianPDFReal _ _).comp
      (measurable_fst.sub (hφ.comp measurable_snd)))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- **Standardisation of the flow density**: `p_φ(σy) = p̂_{φ̂}(y)/σ`. -/
lemma flowPDF_mul_sigma {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    M.flowPDF φ (M.σ * y) = flowDensity (M.stdStrategy φ) y / M.σ := by
  have hmeas : AEStronglyMeasurable
      (fun v => gaussianPDFReal 0 M.noiseVar (M.σ * y - φ v)) M.valueLaw :=
    ((measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub hφ)).aestronglyMeasurable
  have hpt : ∀ t : ℝ, gaussianPDFReal 0 M.noiseVar (M.σ * y - φ (M.μ₀ + M.τ * t))
      = stdNormalPDF (y - M.stdStrategy φ t) / M.σ := by
    intro t
    rw [← M.mul_stdStrategy φ t,
      show M.σ * y - M.σ * M.stdStrategy φ t = M.σ * (y - M.stdStrategy φ t) by ring,
      gaussianPDFReal_mul_of_pos M.hσ (v := M.noiseVar) rfl, ← stdNormalPDF_apply]
  rw [flowPDF_def, M.integral_valueLaw_std hmeas]
  simp only [hpt]
  rw [integral_div]
  rfl

/-- **Standardisation of the value-weighted flow density**:
`n_φ(σy) = (μ₀·p̂(y) + τ·n̂(y))/σ`. -/
lemma flowNum_mul_sigma {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    M.flowNum φ (M.σ * y)
      = (M.μ₀ * flowDensity (M.stdStrategy φ) y
          + M.τ * ∫ t, t * stdNormalPDF (y - M.stdStrategy φ t) ∂gaussianReal 0 1)
        / M.σ := by
  have hψ : Measurable (M.stdStrategy φ) := M.measurable_stdStrategy hφ
  have hmeas : AEStronglyMeasurable
      (fun v => v * gaussianPDFReal 0 M.noiseVar (M.σ * y - φ v)) M.valueLaw :=
    (measurable_id.mul ((measurable_gaussianPDFReal _ _).comp
      (measurable_const.sub hφ))).aestronglyMeasurable
  have hb1 : Integrable (fun t => stdNormalPDF (y - M.stdStrategy φ t))
      (gaussianReal 0 1) := by
    have h := stdModel.integrable_noisePDF_comp hψ y
    rw [stdModel_noiseVar, stdModel_valueLaw] at h
    exact h
  have hb2 : Integrable (fun t => t * stdNormalPDF (y - M.stdStrategy φ t))
      (gaussianReal 0 1) := by
    have h := stdModel.integrable_id_mul_noisePDF_comp hψ y
    rw [stdModel_noiseVar, stdModel_valueLaw] at h
    exact h
  have hI1 : Integrable (fun t => M.μ₀ * stdNormalPDF (y - M.stdStrategy φ t))
      (gaussianReal 0 1) := hb1.const_mul M.μ₀
  have hI2 : Integrable
      (fun t => M.τ * (t * stdNormalPDF (y - M.stdStrategy φ t)))
      (gaussianReal 0 1) := hb2.const_mul M.τ
  have hpt : ∀ t : ℝ, (M.μ₀ + M.τ * t)
        * gaussianPDFReal 0 M.noiseVar (M.σ * y - φ (M.μ₀ + M.τ * t))
      = (M.μ₀ * stdNormalPDF (y - M.stdStrategy φ t)
          + M.τ * (t * stdNormalPDF (y - M.stdStrategy φ t))) / M.σ := by
    intro t
    rw [← M.mul_stdStrategy φ t,
      show M.σ * y - M.σ * M.stdStrategy φ t = M.σ * (y - M.stdStrategy φ t) by ring,
      gaussianPDFReal_mul_of_pos M.hσ (v := M.noiseVar) rfl, ← stdNormalPDF_apply]
    ring
  rw [flowNum_def, M.integral_valueLaw_std hmeas]
  simp only [hpt]
  rw [integral_div, integral_add hI1 hI2, integral_const_mul, integral_const_mul]
  rfl

/-- The order-flow density of a general Kyle model is everywhere positive
(Lemma 2.1 at general `(μ₀, τ, σ)`, obtained from the normalised statement
by the standardisation above). -/
lemma flowPDF_pos {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) : 0 < M.flowPDF φ y := by
  have hσ : M.σ ≠ 0 := M.hσ.ne'
  have h : M.σ * (y / M.σ) = y := by field_simp
  rw [← h, M.flowPDF_mul_sigma hφ]
  exact div_pos (lemma21_flowDensity_pos (M.measurable_stdStrategy hφ) _) M.hσ

lemma measurable_bayesPrice {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (M.bayesPrice φ) :=
  (M.measurable_flowNum hφ).div (M.measurable_flowPDF hφ)

/-- The Bayes quotient is a pricing rule for `φ` on a general Kyle model
(the general-`M` form of `lemma21_isPricingRule`). -/
lemma isPricingRule_bayesPrice {φ : ℝ → ℝ} (hφ : Measurable φ) :
    M.IsPricingRule φ (M.bayesPrice φ) := by
  refine M.isPricingRule_of_forall_mul_flowPDF hφ (M.measurable_bayesPrice hφ)
    fun y => ?_
  exact div_mul_cancel₀ _ (M.flowPDF_pos hφ y).ne'

/-- **Standardisation of the pricing rule** (v4 §7's `P̂`, read backwards):
`P₀(σy) = μ₀ + τ·P̂(y)` where `P̂ = inverseRegression φ̂` is §2's normalised
inverse regression for the standardised strategy. -/
lemma bayesPrice_mul_sigma {φ : ℝ → ℝ} (hφ : Measurable φ) (y : ℝ) :
    M.bayesPrice φ (M.σ * y)
      = M.μ₀ + M.τ * inverseRegression (M.stdStrategy φ) y := by
  have hσ : M.σ ≠ 0 := M.hσ.ne'
  have hp : 0 < flowDensity (M.stdStrategy φ) y :=
    lemma21_flowDensity_pos (M.measurable_stdStrategy hφ) y
  have hpne : flowDensity (M.stdStrategy φ) y ≠ 0 := hp.ne'
  unfold bayesPrice inverseRegression
  rw [M.flowPDF_mul_sigma hφ, M.flowNum_mul_sigma hφ]
  field_simp

/-- The insider's expected price at a rescaled order: the `L¹` input to the
profit computation. -/
lemma integrable_bayesPrice_comp {φ : ℝ → ℝ} (hφ : Measurable φ) (x : ℝ) :
    Integrable (fun ω => M.bayesPrice φ (M.σ * x + M.U ω)) M.μ := by
  have hQx : Measurable fun u => M.bayesPrice φ (M.σ * x + u) :=
    (M.measurable_bayesPrice hφ).comp (measurable_const_add _)
  have hsh : Integrable
      (fun s => inverseRegression (M.stdStrategy φ) (x + s)) (gaussianReal 0 1) :=
    integrable_inverseRegression_shift (M.measurable_stdStrategy hφ) x
  have hA : Integrable
      (fun s => M.μ₀ + M.τ * inverseRegression (M.stdStrategy φ) (x + s))
      (gaussianReal 0 1) := (integrable_const M.μ₀).add (hsh.const_mul M.τ)
  have hstd : Integrable (fun s => M.bayesPrice φ (M.σ * x + M.σ * s))
      (gaussianReal 0 1) := by
    refine hA.congr ?_
    filter_upwards with s
    rw [show M.σ * x + M.σ * s = M.σ * (x + s) by ring, M.bayesPrice_mul_sigma hφ]
  have hmap : Measurable fun s : ℝ => M.σ * s := by fun_prop
  have hnoise : Integrable (fun u => M.bayesPrice φ (M.σ * x + u)) M.noiseLaw := by
    rw [← M.map_std_noiseLaw, integrable_map_measure
      (by rw [M.map_std_noiseLaw]; exact hQx.aestronglyMeasurable) hmap.aemeasurable]
    exact hstd
  exact (integrable_map_measure (μ := M.μ)
    (by rw [M.map_U]; exact hQx.aestronglyMeasurable) M.hU.aemeasurable).mp
    (by rw [M.map_U]; exact hnoise)

/-- **Standardisation of the expected price**: `E[P₀(σx + U)] = μ₀ + τ·F̂(x)`
where `F̂ = gaussianSmoothing φ̂` is §2's normalised smoothing of the
standardised strategy (v4 §7's `P̂`-identity, integrated). -/
lemma integral_bayesPrice_comp {φ : ℝ → ℝ} (hφ : Measurable φ) (x : ℝ) :
    ∫ ω, M.bayesPrice φ (M.σ * x + M.U ω) ∂M.μ
      = M.μ₀ + M.τ * gaussianSmoothing (M.stdStrategy φ) x := by
  have hQx : Measurable fun u => M.bayesPrice φ (M.σ * x + u) :=
    (M.measurable_bayesPrice hφ).comp (measurable_const_add _)
  have hsh : Integrable
      (fun s => inverseRegression (M.stdStrategy φ) (x + s)) (gaussianReal 0 1) :=
    integrable_inverseRegression_shift (M.measurable_stdStrategy hφ) x
  have h1 : ∫ ω, M.bayesPrice φ (M.σ * x + M.U ω) ∂M.μ
      = ∫ u, M.bayesPrice φ (M.σ * x + u) ∂M.noiseLaw := by
    conv_rhs => rw [← M.map_U]
    exact (integral_map M.hU.aemeasurable
      (by rw [M.map_U]; exact hQx.aestronglyMeasurable)).symm
  have h2 : ∫ u, M.bayesPrice φ (M.σ * x + u) ∂M.noiseLaw
      = ∫ s, M.bayesPrice φ (M.σ * x + M.σ * s) ∂gaussianReal 0 1 :=
    M.integral_noiseLaw_std hQx.aestronglyMeasurable
  have h3 : ∀ s : ℝ, M.bayesPrice φ (M.σ * x + M.σ * s)
      = M.μ₀ + M.τ * inverseRegression (M.stdStrategy φ) (x + s) := fun s => by
    rw [show M.σ * x + M.σ * s = M.σ * (x + s) by ring, M.bayesPrice_mul_sigma hφ]
  rw [h1, h2]
  simp only [h3]
  rw [integral_add (integrable_const M.μ₀) (hsh.const_mul M.τ), integral_const,
    integral_const_mul]
  simp only [probReal_univ, one_smul]
  rfl

/-- **The profit rescaling of v4 §7**: against the canonical pricing rule,
`E[(μ₀ + τv − P₀(σx + U))·σx] = στ · x(v − F̂(x))`, i.e. the insider's
expected profit in the original model at `(v, x)` rescaled is exactly `στ`
times the normalised objective of the standardised strategy. -/
lemma expectedProfit_bayesPrice {φ : ℝ → ℝ} (hφ : Measurable φ) (v x : ℝ) :
    M.expectedProfit (M.bayesPrice φ) (M.μ₀ + M.τ * v) (M.σ * x)
      = M.σ * M.τ * objective 0 (M.stdStrategy φ) v x := by
  have hint := M.integrable_bayesPrice_comp hφ x
  have hval := M.integral_bayesPrice_comp hφ x
  have hmul : Integrable
      (fun ω => M.σ * x * M.bayesPrice φ (M.σ * x + M.U ω)) M.μ :=
    hint.const_mul (M.σ * x)
  have hrw : (fun ω => (M.μ₀ + M.τ * v
        - M.bayesPrice φ (M.σ * x + M.U ω)) * (M.σ * x))
      = fun ω => (M.μ₀ + M.τ * v) * (M.σ * x)
          - M.σ * x * M.bayesPrice φ (M.σ * x + M.U ω) := by
    funext ω
    ring
  unfold expectedProfit
  rw [hrw, integral_sub (integrable_const _) hmul, integral_const,
    integral_const_mul, hval]
  simp only [probReal_univ, one_smul]
  unfold objective
  ring

end KyleModel

/-- Uniqueness direction of **v4 Theorem 1.1** (strategy half): every
equilibrium strategy — Borel, with no regularity or moment assumption —
equals Kyle's affine strategy (eq. (1.1)), exactly (at every `v`, not merely
a.e.). -/
theorem isEquilibrium_eq_kyleStrategy (M : KyleModel Ω) (φ : ℝ → ℝ)
    (hφ : M.IsEquilibriumStrategy φ) : φ = M.kyleStrategy := by
  obtain ⟨hm, P, hP, hmax⟩ := hφ
  have hσ : M.σ ≠ 0 := M.hσ.ne'
  have hτ : M.τ ≠ 0 := M.hτ.ne'
  -- Version-independence: run the argument against the canonical Bayes
  -- quotient `P₀ = n_φ/p_φ`, which agrees with `P` off a Lebesgue-null set
  -- because `p_φ > 0` everywhere.
  have hae : P =ᵐ[(volume : Measure ℝ)] M.bayesPrice φ :=
    M.pricingRule_ae_eq_of_flowPDF_pos hm hP (M.isPricingRule_bayesPrice hm)
      (M.flowPDF_pos hm)
  -- The standardised strategy satisfies the pointwise-maximisation
  -- condition (17): profits rescale by the positive constant `στ`, and
  -- `v ↦ μ₀ + τv`, `x ↦ σx` are bijections.
  have hgam : IsGammaSolution 0 (M.stdStrategy φ) := by
    refine ⟨M.measurable_stdStrategy hm, fun v x => ?_⟩
    have h1 := hmax (M.μ₀ + M.τ * v) (M.σ * x)
    simp only [expectedProfit_congr_ae M hae] at h1
    rw [← M.mul_stdStrategy φ v, M.expectedProfit_bayesPrice hm v x,
      M.expectedProfit_bayesPrice hm v (M.stdStrategy φ v)] at h1
    exact le_of_mul_le_mul_left h1 (mul_pos M.hσ M.hτ)
  -- v4 Theorem 7.1 on the standardised strategy, then undo the rescaling.
  have hid : M.stdStrategy φ = id := (isGammaSolution_zero_iff _).1 hgam
  funext v
  have h : φ (M.μ₀ + M.τ * ((v - M.μ₀) / M.τ)) / M.σ = (v - M.μ₀) / M.τ :=
    congrFun hid ((v - M.μ₀) / M.τ)
  rw [show M.μ₀ + M.τ * ((v - M.μ₀) / M.τ) = v by field_simp; ring] at h
  have h' : φ v * M.τ = (v - M.μ₀) * M.σ := (div_eq_div_iff hσ hτ).1 h
  have hks : M.kyleStrategy v = M.σ / M.τ * (v - M.μ₀) := rfl
  rw [hks, div_mul_eq_mul_div, eq_div_iff hτ]
  linear_combination h'

/-- **v4 Theorem 1.1**, strategy-only iff: for independent `V ~ N(μ₀, τ²)`
and `U ~ N(0, σ²)` with `τ, σ > 0`, a Borel strategy is an equilibrium
strategy iff it is Kyle's affine strategy `φ(v) = (σ/τ)(v − μ₀)`
(eq. (1.1)).
Assembled from the two halves above; no `sorry` of its own. -/
theorem kyle_unique_equilibrium (M : KyleModel Ω) (φ : ℝ → ℝ) :
    M.IsEquilibriumStrategy φ ↔ φ = M.kyleStrategy :=
  ⟨isEquilibrium_eq_kyleStrategy M φ, by
    rintro rfl
    exact kyleStrategy_isEquilibrium M⟩

/-- **v4 Theorem 1.1**, `∃!`-form: the one-period Kyle model has one
equilibrium strategy. Assembled; no `sorry` of its own. -/
theorem kyle_existsUnique_equilibrium (M : KyleModel Ω) :
    ∃! φ : ℝ → ℝ, M.IsEquilibriumStrategy φ :=
  ⟨M.kyleStrategy, kyleStrategy_isEquilibrium M,
    fun ψ hψ => isEquilibrium_eq_kyleStrategy M ψ hψ⟩

/-! ## Theorem 1.1: the pair form (the headline) -/

/-- **v4 Theorem 1.1** (the headline, pair form): a pair `(φ, P)` is an
equilibrium if and only if `φ` is Kyle's affine strategy (eq. (1.1)) and
`P(Y_φ) = μ₀ + λ·Y_φ` almost surely (eq. (1.2)), `λ = τ/(2σ)`. Assembled
from the strategy halves, the pricing characterisation and the
version-independence lemmas; no `sorry` of its own. -/
theorem kyle_equilibrium_pair_iff (M : KyleModel Ω) (φ P : ℝ → ℝ)
    (hP : Measurable P) :
    M.IsEquilibrium φ P ↔
      φ = M.kyleStrategy ∧
        ∀ᵐ ω ∂M.μ, P (M.orderFlow φ ω)
          = M.μ₀ + M.priceImpact * M.orderFlow φ ω := by
  constructor
  · intro h
    have hstrat : φ = M.kyleStrategy :=
      isEquilibrium_eq_kyleStrategy M φ h.isEquilibriumStrategy
    subst hstrat
    exact ⟨rfl, pricingRule_ae_orderFlow M h.pricingRule
      (isPricingRule_kylePricingRule M)⟩
  · rintro ⟨rfl, hae⟩
    have hae' : (fun ω => P (M.orderFlow M.kyleStrategy ω)) =ᵐ[M.μ]
        fun ω => M.kylePricingRule (M.orderFlow M.kyleStrategy ω) := hae
    have hpr : M.IsPricingRule M.kyleStrategy P :=
      ⟨hP, hae'.trans (isPricingRule_kylePricingRule M).ae_eq_condExp⟩
    have hvol : P =ᵐ[(volume : Measure ℝ)] M.kylePricingRule :=
      pricingRule_ae_eq_kylePricingRule M hpr
    refine ⟨M.measurable_kyleStrategy, hpr, fun v x => ?_⟩
    rw [expectedProfit_congr_ae M hvol v x,
      expectedProfit_congr_ae M hvol v (M.kyleStrategy v)]
    exact M.expectedProfit_kylePricingRule_le v x

end KyleUniqueness
