# Mathlib API audit — Kyle uniqueness formalization

**Pin audited:** `mathlib @ 81a5d257c8e410db227a6665ed08f64fea08e997` (tag
v4.32.0), the local copy at `.lake/packages/mathlib/` — byte-identical to
formal-mathfin's pin. **Method:** every name below was verified by grepping the
actual pinned source on 2026-08-12 (file:line evidence given). Names the recon
assessed from memory are marked ✔ (confirmed as-named), ≠ (exists under a
different name — correct name given), or **MISSING** (must be built, with a
difficulty estimate). Paths are relative to `Mathlib/`.

**Local only — do not post or push.**

---

## 1. Gaussian measure API surface

The recon's headline warning is confirmed: **`Mathlib.MeasureTheory.Measure.Gaussian`
does not exist at this pin.** Everything lives under
`Mathlib.Probability.Distributions.Gaussian.{Real, Basic, CharFun, Fernique,
Multivariate, HasGaussianLaw.*, IsGaussianProcess.*}` plus
`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`.

| Needed API | Verdict | Evidence (file:line) | Notes |
|---|---|---|---|
| `gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ` | ✔ | Probability/Distributions/Gaussian/Real.lean:222 | defined via `volume.withDensity (gaussianPDF μ v)` for `v ≠ 0` |
| `gaussianPDFReal`, `_pos`, `_nonneg`, `measurable_`, `integrable_`, `integral_…_eq_one` | ✔ | Real.lean:49, 62, 67, 77, 91, 130 | the density workhorse; positivity is `gaussianPDFReal_pos` (needs `v ≠ 0`) |
| `integral_gaussian : ∫ x, exp (−b x²) = √(π/b)` | ✔ | Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:228 | smoke-tested in `KyleUniqueness/Basic.lean` already |
| Mean: `integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ` | ✔ | Real.lean:539 | used in F1 (E U = 0), I1, N1 |
| Variance: `variance_id_gaussianReal : Var[id; gaussianReal μ v] = v` | ✔ | Real.lean:574 | gives `E[Z²] = 1` with `integral_id` (I3, G1 moment dictionary) |
| All moments: `memLp_id_gaussianReal (p : ℝ≥0)` (+ primed ∞-version) | ✔ | Real.lean:579, 584 | `V, U ∈ L^p` for all finite p — powers the moment dictionary |
| Affine maps: `gaussianReal_map_add_const`, `gaussianReal_map_const_mul` | ✔ | Real.lean:309, 329 | exactly the location–scale kit for O1 |
| Convolution: `gaussianReal_conv_gaussianReal` | ✔ | Real.lean:644 | law of `βV + U` in N1 (optional route) |
| Kernel measurability: `measurable_gaussianReal` | ✔ | Real.lean:283 | needed to build `κ v = gaussianReal (φ v) 1` as a `Kernel` (N0) |
| `HasLaw` composition lemmas | ✔ (bonus) | Real.lean:388, 406 | newer `HasLaw` API can shorten O1's plumbing |
| `NoAtoms (gaussianReal μ v)` instance | **MISSING** | grep: no `NoAtoms` in Gaussian/Real.lean | trivial to build (~5 lines): `gaussianReal` is `withDensity` over `volume`, so `μ {a} = 0` via `withDensity_apply` on a singleton; needed by D1, H1, L2. Mini upstream candidate |
| `HasDerivAt (gaussianPDFReal 0 1) (−x·ϱ x) x` | **MISSING** | no derivative lemma for `gaussianPDFReal` in Real.lean | ~10 lines from `Real.exp` chain rule (`Real.hasDerivAt_exp` + `HasDerivAt.comp`); used by D2, F1, I1. Put in `GaussianHelpers.lean` |
| Gaussian tail FTC `∫_{v>a} v·ϱ v = ϱ a` | **MISSING** (as named) | — | direct from `integral_Ioi_of_hasDerivAt_of_tendsto` (below) + the derivative lemma above; shared by A4, F1, I1 |
| Bivariate Gaussian conditional expectation | **MISSING** (no bivariate conditioning API at pin; Multivariate.lean is `IsGaussian` on Banach spaces, no conditioning) | Gaussian/Multivariate.lean | **deliberately avoided** — N1 computes the conditional mean by explicit complete-the-square instead. Do not build |

## 2. Analyticity / entire functions / identity theorem

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| `DifferentiableOn.analyticOnNhd` (ℂ, open set) | ✔ | Analysis/Complex/CauchyIntegral.lean:631 | Cauchy–Goursat: differentiable ⇒ analytic |
| `analyticOnNhd_univ_iff_differentiable` | ✔ | CauchyIntegral.lean:683 | the "entire ⇔ everywhere ℂ-differentiable" bridge — **this is what removes the paper's all-orders induction in A5** |
| Identity theorem, accumulation-point form: `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` | ≠ **location** (name confirmed, file differs from recon's guess) | Analysis/Analytic/**IsolatedZeros.lean**:214 (recon pointed at Uniqueness.lean, which holds the `eventuallyEq` variants at :204/:223 and only *references* the frequently-form in docstrings) | hypotheses: `AnalyticOnNhd 𝕜 f U`, `IsPreconnected U`, `x₀ ∈ U`, `∃ᶠ z in 𝓝[≠] x₀, f z = 0`. Exactly L2's shape. Also available: `eqOn_zero_of_preconnected_of_mem_closure` (:228) — may be even more convenient (zeros set closure form) |
| `AnalyticAt.frequently_zero_iff_eventually_zero` | ✔ (bonus) | IsolatedZeros.lean:136 | alternative local route |
| `AnalyticOnNhd.comp`, `ContinuousLinearMap.analyticAt`, `AnalyticAt.restrictScalars` | ✔ (standard analytic-calculus toolbox; spot-checked namespace exists under Analysis/Analytic/{Composition,Constructions,RestrictScalars}) | — | for the ℂ→ℝ restriction in A5(iii); `Complex.reCLM`, `Complex.ofRealCLM` exist |
| Real-analytic sub-API (`AnalyticOnNhd ℝ`) | ✔ | same files, 𝕜 general | state F's analyticity as `AnalyticOnNhd ℝ F univ` |

**Assessment:** the identity-theorem endgame needs zero new infrastructure. The
A5 entire-extension needs zero *missing* lemmas — its risk is assembly, not gaps.

## 3. Differentiation under the integral sign

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | ✔ | Analysis/Calculus/ParametricIntegral.lean:288 | **variables are `[RCLike 𝕜]` (checked :55–70), so it applies directly with 𝕜 = ℂ** — the complex differentiation under the integral A5 needs is a single instantiation, no porting |
| `hasDerivAt_integral_of_dominated_loc_of_lip` | ✔ | ParametricIntegral.lean:262 | fallback form (Lipschitz bound) |
| Interval version | ✔ | Analysis/Calculus/ParametricIntervalIntegral.lean | not needed if we stay on ℝ-integrals |

Used by: A5 (ℂ), D1 (ℝ, two integrands), continuity variants in A1/A2 via DCT.

## 4. Stieltjes functions / monotone derivative machinery (hard block 2)

This is where the audit **changes the risk assessment**: the recon graded the
"monotone-Stieltjes domination lemma" medium-high / possibly-to-build. The three
lemmas below compose into exactly that domination — it is assemblable, not
buildable-from-scratch.

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| `StieltjesFunction` structure + `.measure` | ✔ | MeasureTheory/Measure/Stieltjes.lean:110, 527ff | `measure_Ioc f a b = ofReal (f b − f a)` :527; `measure_Icc` :571, `measure_singleton` :532, `measure_Iic/Ici` :612/:632 |
| `Monotone.stieltjesFunction` (right-continuous modification) | ✔ | Stieltjes.lean:217 (`noncomputable def _root_.Monotone.stieltjesFunction`; `_eq` :247) | needed since `h`/`f_N` are monotone but not a priori right-continuous |
| `Monotone.countable_leftLim_ne` / countable discontinuities | ✔ | Stieltjes.lean:252 (`countable_leftLim_ne`); `Monotone.countable_not_continuousAt` Topology/Order/Monotone.lean:152 | modification-bookkeeping (I1, I2, B1) |
| **`StieltjesFunction.ae_hasDerivAt`**: a.e. `HasDerivAt f ((rnDeriv f.measure volume x).toReal) x` | ✔ | Analysis/Calculus/Monotone.lean:67 | **the a.e. derivative IS the Radon–Nikodym derivative** — the key identification |
| **`Monotone.ae_hasDerivAt`** (same for plain monotone f, w.r.t. `hf.stieltjesFunction.measure`) | ✔ | Monotone.lean:133 | direct form for `h` |
| `Monotone.ae_differentiableAt` | ✔ | Monotone.lean:209 | recon cited this correctly |
| **`withDensity_rnDeriv_le : ν.withDensity (μ.rnDeriv ν) ≤ μ`** | ✔ | MeasureTheory/Measure/Decomposition/Lebesgue.lean:203 | **the domination**: the AC part of the Stieltjes measure is ≤ the whole measure; the singular part is what the paper's BV citation discards |
| `lintegral_withDensity_eq_lintegral_mul`, `lintegral_mono'` | ✔ (core measure theory) | MeasureTheory/Measure/WithDensity.lean; Lebesgue integral files | glue: `∫⁻ g·f′ = ∫⁻ g d(withDensity) ≤ ∫⁻ g dμ_f` |
| Stieltjes **integration by parts** `∫ ϱ dμ_f = E[Z f(Z)]` (f bounded monotone) | **MISSING** | no Stieltjes IBP in Stieltjes.lean or IntegrationByParts files | **build via layer-cake Fubini** (blueprint I1): `measure_Ioc` + Tonelli + Gaussian tail FTC. ~200–300 LOC, standard difficulty. Upstream candidate `StieltjesFunction.integral_gaussianPDF_eq` |
| BV theory (Ambrosio–Fusco–Pallara §3.2, cited by the paper) | **MISSING and NOT NEEDED** | no BV decomposition of monotone functions at pin (`Mathlib/Analysis/BoundedVariation.lean` covers variation of functions, not the measure decomposition) | the rnDeriv route above replaces it entirely |

## 5. Stein-type identities

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| Smooth Stein identity `E[Z f(Z)] = E[f′(Z)]` | **MISSING** (no Stein identity anywhere in Probability/ at pin; grep for "Stein" returns nothing relevant) | — | derive per-instance: F1 (for `P`, C¹ case) via interval IBP + boundary decay; I1+I2+I3 (monotone case, one-sided). Confirmed prime upstream candidates: `ProbabilityTheory.integral_id_mul_eq_integral_deriv_gaussian` (smooth) and the monotone inequality (I3) |
| Exchangeable-pair / Stein's-method library | **MISSING** (expected) | — | not needed as a library: E1/E2 build the concrete measure on ℝ³; only Fubini/Tonelli identities used |
| `ProbabilityTheory.covariance` | ✔ (bonus — recon didn't know) | Probability/Moments/Covariance.lean:44 | can state D1's `P′ = Cov_{π_y}(id, φ)` against the actual Mathlib `covariance`; also `covarianceBilin` variants exist |

## 6. Conditional expectation / conditional distribution

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| `MeasureTheory.condExp` (`μ[f|m]`) + `integral_condExp` | ✔ | MeasureTheory/Function/ConditionalExpectation/Basic.lean:236 | tower/laws-of-total-expectation |
| `condExp_condExp_of_le` | ✔ | Basic.lean:344 | tower property |
| Pull-out: `condExp_mul_of_aestronglyMeasurable_left` (+ 3 variants) | ✔ | ConditionalExpectation/PullOut.lean:235–251 | for (21) if the condExp route is taken |
| L²-contraction: `eLpNorm_condExp_le_eLpNorm` | ≠ (recon said "L²-contraction of condExp", exact name is this, for `1 ≤ p`) | ConditionalExpectation/Real.lean:288 | gives `‖P(Y)‖₂ ≤ ‖V‖₂` — or avoid via the direct Cauchy–Schwarz route (blueprint P1) |
| `ProbabilityTheory.condDistrib` | ✔ | Probability/Kernel/CondDistrib.lean | regular conditional distribution via `StandardBorelSpace` |
| **`condDistrib_ae_eq_of_measure_eq_compProd`** | ✔ | CondDistrib.lean:163 (+ :147 measurable version, :177 iff form) | **the faithfulness bridge**: "if the joint law is `lawY ⊗ₘ κ` then `κ` is the conditional distribution" — certifies the explicit posterior `π` (node P1) |
| `condExp_ae_eq_integral_condDistrib` | ✔ | CondDistrib.lean:381 (+ `'` variant :389) | links `P y = ∫ v ∂π_y` (eq. (10)) to `E[V|Y]` |
| Disintegration of a joint density into posterior kernel | partial | Probability/Kernel/Composition/{MeasureCompProd, RadonNikodym, AbsolutelyContinuous}.lean | we never need abstract disintegration — `μJoint = lawY ⊗ₘ π` is proven by hand (Tonelli), then fed to `condDistrib_ae_eq_of_measure_eq_compProd` |

## 7. Integration toolbox (Fubini, IBP, convergence, inequalities)

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| Interval IBP: `intervalIntegral.integral_deriv_mul_eq_sub` family | ✔ | MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:47–142 (recon's memory of the names was right; the FILE moved under IntervalIntegral/) | D2, F1 boundary-term arguments |
| Improper FTC/IBP: `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` (+ `_of_nonneg`, Iic duals) | ✔ | MeasureTheory/Integral/IntegralEqImproper.lean:787, 813 | Gaussian tail FTC (A4/F1/I1 helper) |
| FTC-2 on intervals | ✔ (moved) | MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean (recon's `MeasureTheory.Integral.FundThmCalculus` path no longer exists) | B1's `W = ∫ φ` corollary |
| Bochner MCT: `integral_tendsto_of_tendsto_of_monotone` | ✔ | MeasureTheory/Integral/Bochner/Basic.lean:766 | D2, E2, F1 truncation limits |
| `lintegral_iSup` (MCT in ℝ≥0∞), `lintegral_tendsto_of_tendsto_of_monotone` | ✔ | MeasureTheory/Integral/Lebesgue/ (Add.lean:113 for the tendsto form) | E2's possibly-infinite legs |
| DCT: `tendsto_integral_of_dominated_convergence` | ✔ | core | A1, A2, D2, F1, I3 |
| Hölder / Cauchy–Schwarz for integrals: `integral_mul_le_Lp_mul_Lq_of_nonneg` | ≠ (recon said `inner_mul_le_norm_mul_norm` / "MeasureTheory Hölder"; the usable integral form at pin is this, Bochner/Basic.lean; for signed functions apply to `|f|,|g|` + `abs_integral_le`) | MeasureTheory/Integral/Bochner/Basic.lean:1191 | I3's three CS applications, P1, F2, G1 |
| `MemLp.integrable_mul` (f ∈ L^p, g ∈ L^q ⇒ fg ∈ L¹) | ✔ (bonus) | MeasureTheory/Function/L1Space/Integrable.lean:1085 | the moment dictionary's main tool |
| Fubini/Tonelli: `MeasureTheory.integral_prod`, `integral_integral_swap`, `lintegral_prod`, `lintegral_lintegral_swap` | ✔ | MeasureTheory/Constructions/Prod/ + Measure/Prod.lean | E1, E2, F2, I1 |
| compProd: `Measure.compProd`, `Measure.lintegral_compProd` | ✔ | Probability/Kernel/Composition/MeasureCompProd.lean:183 | N0, E1, L1 |
| Bochner compProd: `ProbabilityTheory.integral_compProd` + `Integrable.integral_compProd` | ✔ | Probability/Kernel/Composition/IntegralCompProd.lean:29, :150 | test-function identities in E2/P1 |
| a.e. fibrewise from a.e. joint: `Measure.ae_compProd_iff` / `Measure.ae_ae_of_ae_compProd` | ✔ | Probability/Kernel/Composition/MeasureCompProd.lean:118 (`ae_ae_of_ae_compProd`), :123 (`ae_compProd_iff`) | L1's conditioning step |
| `integral_map` | ✔ | Bochner/Basic.lean:1043 | O1 change of variables |
| `integral_pos_iff_support_of_nonneg_ae` | ✔ (core) | MeasureTheory/Integral/Bochner | A1 positivity, D1 |

## 8. Convexity, monotonicity, elementary analysis

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| `ConvexOn` toolbox + continuity of convex functions on ℝ | ✔ | Analysis/Convex/Continuous.lean, Slope.lean, Deriv.lean | B1. Note blueprint B1 proves convexity directly from attainment — barely uses the API |
| Abstract subdifferential (`∂W`) | **MISSING** (no subdifferential API for ℝ→ℝ at pin) and **NOT NEEDED** | — | paper's own subgradient inequality is one line; formalize it directly (blueprint B1) |
| `Monotone.strictMono_of_injective` | ✔ (Order.Monotone basic) | core order library | B2 |
| `Monotone.tendsto_atTop_atTop` etc. | ✔ | Order/Monotone + Topology.Order | B2 limits |
| `IsLocalMax.deriv_eq_zero` | ✔ | Analysis/Calculus/LocalExtr/Basic.lean:251 | B2's FOC |
| `strictMonoOn_of_deriv_pos` | ✔ | Analysis/Calculus/MeanValue.lean (consumed at e.g. Analysis/Convex/Deriv.lean:269, BinaryEntropy.lean:369) | M1 cubic |
| `intermediate_value_Icc` | ✔ | Topology/Order/IntermediateValue.lean | M1 |
| `is_const_of_deriv_eq_zero` / `constant_of_derivWithin_zero` | ✔ | Analysis/Calculus/MeanValue.lean | L2's F/x patch |
| `hasDerivAt_iff_tendsto_slope` | ✔ | Analysis/Calculus/Deriv basic | L2 (constants equal F′(0)), B1 |
| `Real.sqrt` API (`sq_sqrt`, `sqrt_pos`, `sqrt_le_sqrt`, `sqrt_mul_self`) | ✔ | Analysis/SpecialFunctions/Sqrt + Pow | H1, G1, I3, J1 |
| AM–GM 2-term (`two_mul_le_add_sq` + `nlinarith`) | ✔ | Mathlib.Algebra.Order.Ring core | G1 (24); `nlinarith`/`polyrith` close the (23)–(26) algebra |
| `Monotone.ae_differentiableAt` | ✔ | Analysis/Calculus/Monotone.lean:209 | (listed again for completeness — recon's citation was correct) |

## 9. Measure-theory odds and ends

| Needed API | Verdict | Evidence | Notes |
|---|---|---|---|
| `IsOpen.measure_pos` (nonempty open has positive volume) | ✔ (core, `Measure.IsOpenPosMeasure` instance for `volume` on ℝ) | MeasureTheory/Measure/OpenPos.lean | A3 |
| `NoAtoms (volume : Measure ℝ)` + null singletons | ✔ (core instance) | — | D1, H1, L2 |
| `NoAtoms` for `withDensity` / pushforward under injective map | **MISSING** as instances | — | two ~5-line glue lemmas (audit §1 note + blueprint L2); trivial |
| Diagonal is null under atomless ⊗ atomless on ℝ | **MISSING** as named | — | ~10 lines by Fubini: `(π ⊗ π) diag = ∫ π {w} dπ = 0`. Needed by D1 |
| Positive-measure subset of ℝ under atomless measure is infinite | **MISSING** as named | — | contrapositive of `Set.Finite.measure_zero` + `measure_singleton = 0`; ~5 lines. L2 |
| `Set.Countable.measure_zero` | ✔ (core) | — | B1, H1, I2 modification bookkeeping |
| `withDensity_absolutelyContinuous` + null-set equivalence for positive densities | ✔ / small glue | MeasureTheory/Measure/WithDensity.lean | A3's "Law(Y) ≪≫ Lebesgue" |
| `IsCompact` accumulation-point extraction (`IsCompact.exists_clusterPt` family; `AccPt` API in Topology/Perfect + Order) | ✔ (family exists; exact accumulation-point-of-infinite-subset lemma may need ~15 lines of glue via `IsCompact.exists_clusterPt` on a sequence) | Topology/Compactness/ | L2; prototype early (blueprint hard-block table) |

---

## 10. Summary of MISSING items (the complete build list)

Everything the project must create that is not in the pinned Mathlib, with
difficulty:

| # | Item | Blueprint node | Difficulty | LOC est. | Upstreamable? |
|---|---|---|---|---|---|
| 1 | `NoAtoms (gaussianReal μ v)` | D1/H1/L2 | trivial | 5–10 | yes (mini) |
| 2 | `HasDerivAt ϱ (−x·ϱ x) x` for `gaussianPDFReal` | D2/F1/I1 | trivial | 10–20 | yes (mini) |
| 3 | Gaussian tail FTC `∫_{Ioi a} x·ϱ x = ϱ a` | A4/F1/I1 | easy | 20–40 | yes (mini) |
| 4 | `NoAtoms` transfer (withDensity, injective pushforward); diagonal-null; positive-measure ⇒ infinite | D1/L2 | easy | 30–60 | yes (mini) |
| 5 | Stieltjes–Gaussian IBP `∫ ϱ dμ_f = E[Z f(Z)]` (bounded monotone f), layer-cake route | I1 | standard | 200–300 | **yes — headline** |
| 6 | Monotone domination `∫⁻ g·f′ ≤ ∫⁻ g dμ_f` (assembled from `Monotone.ae_hasDerivAt` + `withDensity_rnDeriv_le`) + truncation compatibility `f_N′ = f′·1_{|f|<N}` a.e. | I2 | standard | 150–250 | **yes — headline** |
| 7 | Gaussian reciprocal-derivative inequality (Lemma 5.3 verbatim) | I3 | standard+ | 250–400 | **yes — headline (new Stein-type result in Mathlib)** |
| 8 | Smooth Stein identity for C¹ P with linear growth (eq. (22)) | F1 | standard | 100–200 | yes |
| 9 | Everything Kyle-specific (A1–A5, B, D, E, F2–O1) | all | per blueprint | ~5,500–8,000 | no (paper-specific) — except A5's "Gaussian smoothing of linear-growth function is entire", which is upstreamable |

**Net risk view vs. recon:** two of the recon's medium-high items got cheaper
(identity theorem: exists exactly as needed; Stieltjes domination: assemblable
from three pin-present lemmas), one got confirmed-hard (A4/A5 appendix), and no
new gaps surfaced. No item requires original mathematics beyond the paper.

## 11. Loogle cross-check note

Loogle (`loogle.lean-lang.org`) indexes Mathlib master, which has drifted from
v4.32.0; grep-of-pin was used as the source of truth throughout, and loogle was
not relied on for any verdict above. When agents propose lemma names during
proving, **verify against the local pin** (`grep -rn` in
`.lake/packages/mathlib/Mathlib`), not against loogle/moogle output — master
names may not exist at our pin (the `Measure.Gaussian` ghost module is the
canonical example of this failure mode).

## 12. Post-audit addendum (2026-08-12): canary-phase corrections + v3 impact

Corrections discovered while PROVING against the pin during the canary phase
(source: `../CANARY_REPORT.md`), plus the effect of the paper's v3 rewrite
(source: the v2 → v3 reconciliation plan (private working archive)). These supersede the corresponding
rows above; the sections above are otherwise left as the historical v2-keyed
audit record.

1. **§10 item 1 was NOT missing — atoms API renamed.** At this pin the
   atoms typeclass is `MeasureTheory.NullSingletonClass` (`NoAtoms` survives
   only as a deprecated alias dated 2026-06-09), and
   `ProbabilityTheory.nullSingletonClass_gaussianReal` (for `v ≠ 0`) already
   exists — the audit's case-sensitive grep for `NoAtoms` missed it. Also
   present under the new name: `Set.Countable.measure_zero`,
   `Set.Finite.measure_zero`. The transfer glue (`withDensity`, injective
   pushforward, null diagonal) is now PROVED in
   `KyleUniqueness/GaussianHelpers.lean`.
2. **Bonus find: `exists_accPt_of_nullSingletonClass`** (positive measure ⇒
   accumulation point) already exists at the pin — it replaces the entire
   "positive measure ⇒ infinite ⇒ Bolzano–Weierstrass" chain budgeted in §9
   (last row) for the v2 endgame. (Under v3 this matters less — the
   identity-theorem endgame was deleted from the paper — but the spike file
   `IdentityTheoremSpike.lean` proved the full chain and is retained as
   Mathlib-only infrastructure.)
3. **`integrable_id_gaussianReal` is not at the pin under that name** —
   derived in one line from `memLp_id_gaussianReal`; provided in
   `GaussianHelpers.lean`.
4. **§6 (condExp bridge) is no longer prospective — node P1 is DONE.**
   `ae_eq_condExp_of_forall_setIntegral_eq` carried the direct route exactly
   as §6 predicted; the strategy-generic bridge lives in
   `CondExpBridge.lean` with the master identity in test-function form.
5. **v3 makes §§2–3 (analyticity, ℂ-differentiation) MOOT for the paper.**
   v3 removes all complex analysis; the rows in §2 stay valid as API facts
   but have no consumer. §3's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   is still load-bearing — now at `𝕜 = ℝ` only (node R2).
6. **Newly load-bearing, verified at the pin during reconciliation:**
   `Continuous.ae_eq_iff_eq` (MeasureTheory/Measure/OpenPos.lean:141; used —
   proved — in `eq_kylePricingRule_of_continuous`'s derivation),
   `ae_eq_comp'` (MeasureTheory/Measure/Restrict.lean:680) +
   `gaussianReal_absolutelyContinuous` (Gaussian/Real.lean:254) +
   `gaussianReal_map_const_add` (Gaussian/Real.lean:323) — the three carried
   the now-PROVED `expectedProfit_congr_ae`. For the new Q2 node:
   `Measure.ae_ae_of_ae_compProd` and `measure_preimage_add` (Lebesgue
   translation invariance) both exist at the pin (§9 rows unchanged).
