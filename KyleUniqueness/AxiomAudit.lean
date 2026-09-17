/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Main
import KyleUniqueness.BeyondPaper
import KyleUniqueness.IdentityTheoremSpike

/-!
# Axiom audit

`#print axioms` harness in the style of the formal-mathfin reference repo:
every public statement is audited at every build, so the proof-debt surface
is machine-checked and visible in the build log.

`KyleUniqueness.Main` transitively imports the whole development except the
two leaf modules `BeyondPaper` and `IdentityTheoremSpike`, which are
imported here directly so that their declarations stay under audit.

**Status after Session 3, Stage B (2026-09-16; see `PROVING_LOG.md`): the
formalization has no open obligations.** Session 3 closed the value
function (B1/B2), the posterior (A1b/D1/D2), the resampling measure (E1),
the loss identities (v4 Lemmas 3.1/3.2), the accounting identity
(E2 = v4 Prop 5.1), the signed root (H1), `1 ≤ 2Γ` (J1), the saturation
`Γ = 1/2` (T3 = v4 Prop 6.1), the rigidity theorem (N2 = v4 Thm 7.1) and
finally the location–scale standardisation (O1 = v4 §7), which carries the
headline `isEquilibrium_eq_kyleStrategy` (v4 Theorem 1.1, strategy half).

* **Fully proved** (`propext`, `Classical.choice`, `Quot.sound` only):
  **every declaration audited below, without exception** — in particular
  all of Lemmas 2.1–2.3 (`lemma21_*`, `lemma22_memLp_two`,
  `lemma23_integrable`), the `σ = τ = 1` bridge
  (`equilibrium_iff_zeroSolution`), all four Proposition-2 statements
  (`integrable_noiseTraderLoss`, `noiseTraderLoss_le_half`,
  `noiseTraderLoss_eq_half_iff`, `noiseTraderLoss_eq_neg_half_iff`), the
  affine regression layer (`inverseRegression_affine`/`_id`,
  `gaussianSmoothing_affine`/`_id`), the pricing half of Theorem 1
  (`pricingRule_ae_eq_kylePricingRule`, `eq_kylePricingRule_of_continuous`),
  the order-flow law identity (`KyleModel.map_orderFlow` + consumers), the
  Gaussian helper layer, the pricing-rule bridge, the beyond-paper layer,
  the identity-theorem spike, both canaries, every declaration of the six
  Session-3 modules (`ValueFunction`, `Posterior`, `Resampling`, `Loss`,
  `Accounting`, `SignedRoot`), the saturation `gamma_eq_half`, the rigidity
  theorem `isGammaSolution_zero_iff` with its `∃!`-packaging
  `existsUnique_zeroSolution`, the Stage-B standardisation layer
  (`KyleModel.stdStrategy`, `KyleModel.bayesPrice` and the `*_mul_sigma`
  family) and all four forms of the headline
  (`isEquilibrium_eq_kyleStrategy`, `kyle_unique_equilibrium`,
  `kyle_existsUnique_equilibrium`, `kyle_equilibrium_pair_iff`).
* **Open obligations** (additionally `sorryAx`): **none.** No declaration
  anywhere in the development uses `sorry`; `sorryAx` must not appear in
  any line of this file's build output.
-/

open KyleUniqueness

-- Beyond-paper layer (fully proved; v2-legacy, NOT v3 claim surface).
#print axioms cubic_strictMonoOn
#print axioms cubic_pos_root_existsUnique
#print axioms betaGamma_pos
#print axioms betaGamma_root
#print axioms betaGamma_unique
#print axioms betaGamma_zero
#print axioms betaGamma_le_one
#print axioms lambdaGamma
#print axioms lambdaGamma_zero

-- Model layer (fully proved).
#print axioms stdModel
#print axioms stdModel_kyleStrategy
#print axioms KyleModel.IsEquilibrium.isEquilibriumStrategy
#print axioms KyleModel.isEquilibriumStrategy_iff_exists

-- Lemmas 2.1–2.3 bridge statements (ALL PROVED as of 2026-08-12).
#print axioms lemma21_flowDensity_pos
#print axioms lemma21_isPricingRule
#print axioms lemma21_continuous
#print axioms lemma22_memLp_two
#print axioms lemma23_integrable
#print axioms lemma21_unique_continuous_version
#print axioms equilibrium_iff_zeroSolution

-- Proposition 2 (the Γ layer; ALL PROVED as of 2026-08-12).
#print axioms noiseTraderLoss
#print axioms integrable_noiseTraderLoss
#print axioms noiseTraderLoss_le_half
#print axioms noiseTraderLoss_eq_half_iff
#print axioms noiseTraderLoss_eq_neg_half_iff

-- Theorem 4 = v4 Theorem 7.1 (CLOSED in Session 3, both directions; the
-- declarations now live in `KyleUniqueness.Main`) + affine regression.
#print axioms isGammaSolution_zero_iff
#print axioms existsUnique_zeroSolution
#print axioms inverseRegression_affine
#print axioms inverseRegression_id
#print axioms gaussianSmoothing_affine
#print axioms gaussianSmoothing_id

-- Theorem 1, strategy layer and eq. (2). `isEquilibrium_eq_kyleStrategy`
-- (in `KyleUniqueness.Main`) was the last open obligation; node O1 closed
-- it in Session 3 Stage B, so nothing in this file carries `sorryAx`.
#print axioms kyleStrategy_isEquilibrium
#print axioms isEquilibrium_eq_kyleStrategy
#print axioms kyle_unique_equilibrium
#print axioms kyle_existsUnique_equilibrium
#print axioms isPricingRule_kylePricingRule
#print axioms pricingRule_ae_eq_kylePricingRule
#print axioms eq_kylePricingRule_of_continuous

-- Theorem 1, pair form (v3 headline) and its glue.
#print axioms kyleStrategy_kylePricingRule_isEquilibrium
#print axioms pricingRule_ae_orderFlow
#print axioms expectedProfit_congr_ae
#print axioms kyle_equilibrium_pair_iff

-- Canary-phase infrastructure (all fully proved; no `sorryAx` expected).
-- Gaussian helper layer (audit §10 items 2–4 + the toolkit).
#print axioms hasDerivAt_gaussianPDFReal
#print axioms integral_Ioi_id_mul_gaussianPDFReal_std
#print axioms NullSingletonClass.withDensity
#print axioms nullSingletonClass_map_of_injective
#print axioms measure_prod_diagonal_eq_zero
#print axioms infinite_of_measure_ne_zero
#print axioms integral_comp_add_gaussianReal
#print axioms lintegral_comp_add_gaussianReal
#print axioms integral_id_mul_gaussianPDFReal
#print axioms gaussianPDFReal_mul_gaussianPDFReal_kyle
-- Tier-1/2 session additions to the Gaussian helper layer (all proved).
#print axioms gaussianPDFReal_std_anti
#print axioms gaussianPDFReal_std_neg
#print axioms gaussianPDFReal_std_mul_eq_exp_mul
#print axioms lintegral_gaussianPDFReal_std_mul_div
#print axioms gaussianPDFReal_mul_gaussianPDFReal_std
#print axioms integral_mul_self_gaussianReal_std
#print axioms ae_volume_of_ae_gaussianReal
-- The pricing-rule bridge (blueprint node P1, direct route).
#print axioms KyleModel.integral_mul_orderFlow_eq
#print axioms KyleModel.isPricingRule_of_forall_mul_flowPDF
#print axioms KyleModel.kylePricingRule_mul_flowPDF
#print axioms KyleModel.expectedProfit_kylePricingRule
#print axioms KyleModel.expectedProfit_kylePricingRule_le
#print axioms measurable_inverseRegression
-- The order-flow law identity (Tier-1 session; Lemma 2.1's law clause).
#print axioms KyleModel.measurable_flowPDF
#print axioms KyleModel.lintegral_ofReal_kernel_eq_flowPDF
#print axioms KyleModel.map_orderFlow
#print axioms KyleModel.pricingRule_ae_eq_of_flowPDF_pos
#print axioms stdModel_noiseLaw
-- Identity-theorem spike (Tier 0.4; v3 deleted its consumer, hard block 5 —
-- retained as proved Mathlib-only infrastructure, see the file header).
#print axioms analyticOnNhd_eq_zero_of_accPt
#print axioms analyticOnNhd_eq_zero_of_measure_ne_zero
-- The Stein pipeline (blueprint I1–I3 = v3 Lemma 2.5, hard block 2;
-- Mathlib-only file, all proved — session 2).
#print axioms integral_gaussianPDFReal_stieltjesMeasure
#print axioms integral_gaussianPDFReal_stieltjesMeasure_of_monotone
#print axioms ae_indicator_ofReal_deriv_le_rnDeriv
#print axioms lintegral_indicator_ofReal_deriv_mul_le
#print axioms lintegral_ofReal_deriv_mul_le
#print axioms ae_hasDerivAt_clamp_of_abs_lt
#print axioms one_le_lintegral_sq_mul_lintegral_inv_sq
#print axioms one_le_integral_sq_mul_integral_inv_sq
#print axioms one_le_sqrt_integral_sq_mul_integral_inv_sq
-- Node R2 (v3 Lemma 2.3, regularity: `F ∈ C¹` + eq. (5)) — session 2.
#print axioms exp_mul_gaussianPDFReal_std
#print axioms abs_mul_gaussianPDFReal_std_le
#print axioms gaussianPDFReal_std_shift_le
#print axioms abs_sub_mul_gaussianPDFReal_std_le
#print axioms gaussianSmoothing_eq_convolution
#print axioms integrable_gaussianSmoothing_deriv_kernel
#print axioms hasDerivAt_gaussianSmoothing
#print axioms deriv_gaussianSmoothing_eq_prob
#print axioms continuous_gaussianSmoothing_deriv
#print axioms deriv_gaussianSmoothing
#print axioms continuous_deriv_gaussianSmoothing
-- Node D1, C¹ legs (v3 Lemma 4.1, differentiation of n, p, and P) — session 2.
#print axioms abs_mul_gaussianPDFReal_std_le_const
#print axioms hasDerivAt_flowDensity
#print axioms hasDerivAt_flowNumerator
#print axioms hasDerivAt_inverseRegression

/-! ### Session 3 (2026-09-16): the §4–§6 machinery

All of the following are expected `[propext, Classical.choice, Quot.sound]`.
Numbering is v4's (`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision D1).
-/

-- `ValueFunction.lean` — nodes B1/B2 = v4 Lemma 2.4, eqs. (2.4)–(2.6), (A.1).
#print axioms insiderProfit
#print axioms valueFunction
#print axioms objective_zero
#print axioms insiderProfit_apply
#print axioms isMaxOn_objective
#print axioms objective_le_insiderProfit
#print axioms insiderProfit_eq_iSup
#print axioms continuous_gaussianSmoothing
#print axioms measurable_insiderProfit
#print axioms insiderProfit_nonneg
#print axioms insiderProfit_subgradient
#print axioms insiderProfit_sub_sandwich
#print axioms convexOn_insiderProfit
#print axioms monotone_of_isGammaSolution
#print axioms firstOrderCondition
#print axioms insiderProfit_eq_sq_mul_deriv
#print axioms strictMono_of_isGammaSolution
#print axioms continuous_insiderProfit
#print axioms hasDerivAt_insiderProfit_of_continuousAt
#print axioms ae_hasDerivAt_insiderProfit
#print axioms hasDerivWithinAt_Ioi_insiderProfit
#print axioms intervalIntegrable_of_isGammaSolution
#print axioms insiderProfit_sub_eq_intervalIntegral
#print axioms insiderProfit_id

-- `Posterior.lean` — nodes A1b + D1-rest + D2 = v4 Lemma 2.1, §2.2, Lemma 2.5.
#print axioms jointDensity
#print axioms measurable_jointDensity
#print axioms map_value_orderFlow
#print axioms stdModel_map_value_orderFlow
#print axioms posteriorDensity
#print axioms posterior
#print axioms isProbabilityMeasure_posterior
#print axioms nullSingletonClass_posterior
#print axioms integral_posterior
#print axioms integrable_posterior_iff
#print axioms inverseRegression_eq_integral_posterior
#print axioms integrable_sq_gaussianReal_std
#print axioms memLp_id_posterior
#print axioms memLp_strategy_posterior
#print axioms deriv_inverseRegression_eq_cov
#print axioms integrable_symm
#print axioms integral_symm_eq
#print axioms integral_symm_pos
#print axioms deriv_inverseRegression_eq_symm
#print axioms deriv_inverseRegression_pos
#print axioms strictMono_inverseRegression
#print axioms integral_symm_gaussianSmoothing
#print axioms deriv_gaussianSmoothing_pos
#print axioms strictMono_gaussianSmoothing
#print axioms deriv_gaussianSmoothing_pos_of_strictMono
#print axioms strictMono_gaussianSmoothing_of_strictMono

-- `Resampling.lean` — node E1 + R2b = v4 Lemma 2.6 (i)–(iv), Lemma 2.3 tower.
#print axioms resamplingMeasure
#print axioms isProbabilityMeasure_resamplingMeasure
#print axioms resamplingMeasure_map_swap
#print axioms resamplingMeasure_map_snd
#print axioms resamplingMeasure_map_fst
#print axioms resamplingMeasure_map_v1
#print axioms resamplingMeasure_map_v0
#print axioms resamplingMeasure_map_y
#print axioms integrable_v1_resampling
#print axioms integrable_v0_resampling
#print axioms integrable_inverseRegression_resampling
#print axioms integrable_bayesNumerator_kernel
#print axioms integral_bayesNumerator_kernel
#print axioms integral_v1_mul_eq_inverseRegression
#print axioms integral_v1_mul_eq_gaussianSmoothing
#print axioms integral_v1_mul_comp_eq_gaussianSmoothing
#print axioms integrable_v0_mul_v1_resampling
#print axioms integral_v0_mul_v1_resampling
#print axioms integrable_gaussianSmoothing_comp
#print axioms gaussianSmoothing_comp_ae_eq_condExp_condExp

-- `Loss.lean` — v4 Lemma 3.1 (`Γ = E[F′(φ(V))]`) and Lemma 3.2.
#print axioms deriv_gaussianSmoothing_eq_integral
#print axioms deriv_gaussianSmoothing_comp_eq
#print axioms integrable_deriv_gaussianSmoothing_comp
#print axioms noiseTraderLoss_eq_integral_deriv
#print axioms integral_snd_mul_sub_fst_eq_noiseTraderLoss
#print axioms integral_noise_mul_sub_value_eq_noiseTraderLoss
#print axioms covariance_noise_condExp_eq_noiseTraderLoss
#print axioms integrable_inverseRegression_const_add
#print axioms expectedProfit_inverseRegression
#print axioms objective_eq_expectedProfit
#print axioms noiseTraderLoss_id

-- `Accounting.lean` — node E2 = v4 Proposition 5.1 (the accounting identity).
#print axioms clampAt
#print axioms clampAt_sub_le
#print axioms integral_resampling_swap
#print axioms integral_pair_v0
#print axioms integral_pair_v1
#print axioms integral_v1_mul_eq_inverseRegression_memLp
#print axioms integrable_replica_increment
#print axioms replica_identity
#print axioms integral_clamp_replica_eq
#print axioms clamp_increment_bounds
#print axioms tendsto_clamp_replica
#print axioms ae_clamp_insiderProfit
#print axioms accounting_identity
#print axioms integrable_insiderProfit_of_isGammaSolution
#print axioms noiseTraderLoss_eq_integral_insiderProfit
#print axioms integral_insiderProfit_id

-- `SignedRoot.lean` — node H1 (v4 Prop 6.1's construction) and node J1.
#print axioms criticalPoint
#print axioms strategy_criticalPoint
#print axioms posteriorSlope
#print axioms posteriorSlope_pos
#print axioms noiseTraderLoss_eq_integral_posteriorSlope
#print axioms noiseTraderLoss_pos
#print axioms insiderProfit_criticalPoint
#print axioms insiderProfit_pos_of_ne
#print axioms signedRoot
#print axioms rootSlope
#print axioms signedRoot_sq
#print axioms inv_rootSlope_sq
#print axioms continuous_signedRoot
#print axioms strictMono_signedRoot
#print axioms monotone_signedRoot
#print axioms ae_hasDerivAt_signedRoot
#print axioms integrable_sq_signedRoot_iff
#print axioms integral_sq_signedRoot
#print axioms integrable_inv_sq_rootSlope
#print axioms integral_inv_sq_rootSlope
#print axioms one_le_two_mul_noiseTraderLoss
#print axioms isGammaSolution_zero_id
#print axioms signedRoot_id
#print axioms integral_insiderProfit_id'
#print axioms two_mul_noiseTraderLoss_id
#print axioms one_le_two_mul_noiseTraderLoss_id

-- `Main.lean` — node T3 = v4 Proposition 6.1, and the a.e. → everywhere
-- upgrade that node N2 = v4 Theorem 7.1 consumes. (The six moved headline
-- carriers are audited in their original blocks above.)
#print axioms gamma_eq_half
#print axioms KyleUniqueness.Monotone.eq_of_ae_eq_continuous

/-! ### Session 3, Stage B (2026-09-16): node O1, the location–scale
standardisation (v4 §7, the strategy half of Theorem 1.1)

The layer that reduces a general Kyle model `(μ₀, τ, σ)` to the normalised
model of §2 by a change of variables inside the value- and noise-law
integrals: `V̂ = (V − μ₀)/τ`, `Û = U/σ`, `φ̂(t) = φ(μ₀ + τt)/σ`,
`P̂(y) = (P(σy) − μ₀)/τ`. All expected `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms KyleModel.stdStrategy
#print axioms KyleModel.bayesPrice
#print axioms KyleModel.measurable_stdStrategy
#print axioms KyleModel.mul_stdStrategy
#print axioms KyleModel.map_std_valueLaw
#print axioms KyleModel.map_std_noiseLaw
#print axioms KyleModel.integral_valueLaw_std
#print axioms KyleModel.integral_noiseLaw_std
#print axioms KyleModel.measurable_flowNum
#print axioms KyleModel.flowPDF_mul_sigma
#print axioms KyleModel.flowNum_mul_sigma
#print axioms KyleModel.flowPDF_pos
#print axioms KyleModel.measurable_bayesPrice
#print axioms KyleModel.isPricingRule_bayesPrice
#print axioms KyleModel.bayesPrice_mul_sigma
#print axioms KyleModel.integrable_bayesPrice_comp
#print axioms KyleModel.integral_bayesPrice_comp
#print axioms KyleModel.expectedProfit_bayesPrice
