/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Statement
import KyleUniqueness.Regularity
import KyleUniqueness.PosteriorDeriv
import KyleUniqueness.BeyondPaper
import KyleUniqueness.IdentityTheoremSpike
import KyleUniqueness.SteinInequality

/-!
# Axiom audit

`#print axioms` harness in the style of the formal-mathfin reference repo:
every public statement is audited at every build, so the proof-debt surface
is machine-checked and visible in the build log.

Expected axiom sets after the Tier-1/2 proving session (2026-08-12,
post-reconciliation; see `PROVING_LOG.md`):

* **Fully proved** (`propext`, `Classical.choice`, `Quot.sound` only):
  everything except the two headline uniqueness carriers — in particular
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
  the identity-theorem spike, and both canaries.
* **Open obligations** (additionally `sorryAx`): exactly the two headline
  uniqueness carriers `isGammaSolution_zero_iff` (Theorem 4, rigidity
  direction — its existence direction is proved in-file) and
  `isEquilibrium_eq_kyleStrategy` (Theorem 1, strategy half). Assembled
  theorems (`kyle_unique_equilibrium`, `kyle_existsUnique_equilibrium`,
  `kyle_equilibrium_pair_iff`, `existsUnique_zeroSolution`) carry `sorryAx`
  only through those two names, not through `sorry`s of their own.
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

-- Theorem 4 (rigidity direction open) + affine regression (proved).
#print axioms isGammaSolution_zero_iff
#print axioms existsUnique_zeroSolution
#print axioms inverseRegression_affine
#print axioms inverseRegression_id
#print axioms gaussianSmoothing_affine
#print axioms gaussianSmoothing_id

-- Theorem 1, strategy layer and eq. (2).
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
