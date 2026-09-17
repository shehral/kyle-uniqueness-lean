# STATEMENT_NOTES — Monteiro–Tourky Kyle uniqueness, formalization notes

**Paper:** Monteiro & Tourky, *The one-period Kyle model has one equilibrium*,
arXiv:2607.23585 **v4** (2026-08-20). All §/eq./lemma numbers below are **v4's**
unless explicitly marked v3 or v2. Title history: v2 *"Monotonicity and Rigidity
in Gaussian Inverse Regression — The One-Period Kyle Model Has a Unique
Equilibrium"*; v3 (2026-08-10) *"The one-period Gaussian Kyle model has exactly
one equilibrium"*; v4 dropped "Gaussian"/"exactly" from the title and rewrote the
§4 proof apparatus. The v2 → v3 reconciliation is in `V3_RECONCILIATION_PLAN.md`
+ `RECONCILIATION_REPORT.md` (both now historical); the v3 → v4 reconciliation,
executed 2026-09-16, is in `V4_DELTA_REPORT_2026-09-16.md`.

**Status: COMPLETE — 0 `sorry`, axiom-clean.** Verified against the from-scratch
`lake build` of 2026-09-16, run on the working tree that sits uncommitted on top
of commit `f975dbc` (the figures below do **not** hold at `f975dbc` itself — the
hash must be re-pinned once the closeout is committed):

- `lake build` from deleted project oleans: **exit 0, 3149 jobs**, 0 errors,
  0 warnings, 0 `declaration uses 'sorry'`, 0 `sorryAx`. The only non-axiom
  diagnostic in the 434-line log is a pre-existing info-level `ring_nf`
  suggestion at `Regularity.lean:77:2`. (434 lines when only
  `.lake/build/lib/lean/KyleUniqueness/` is deleted; 435 with the §7 recipe,
  which also deletes the umbrella oleans and so re-emits the final
  `Built KyleUniqueness` line.)
- 19 Lean files, 10,120 lines.
- `KyleUniqueness/AxiomAudit.lean` emits 399 `#print axioms` lines; the set of
  distinct axiom lists has cardinality **one**: `[propext, Classical.choice,
  Quot.sound]`. Independently re-checked out of tree for all 26 public
  `Main.lean` declarations plus 53 further headline carriers (79 total).
- No project-local `axiom`, no `native_decide`, no `unsafe`/`partial`/`opaque`/
  `@[extern]`/`@[implemented_by]`, no `set_option` suppressions, no
  `TODO`/`FIXME`/`nolint`. The 16 grep hits for "sorry" are all inside
  docstrings or comments.
- Lint: `weak.linter.mathlibStandardSet` runs under `lake build` and is clean.
  The Batteries **environment** linter is wired into `lakefile.lean`
  (`lintDriver := "batteries/runLinter"`, `lintDriverArgs := #["KyleUniqueness"]`);
  `lake lint` exits 0 with `-- Linting passed for KyleUniqueness.` — zero
  findings. The one pre-existing finding it used to report (an unused
  `[SFinite μ]` instance argument on `measure_prod_diagonal_eq_zero`,
  `GaussianHelpers.lean`) was fixed at closeout by removing the argument.

**Local only — nothing published, pushed, or announced.**

---

## 0. The artifact

Headline declarations live in **`KyleUniqueness/Main.lean`**:
`kyle_equilibrium_pair_iff` (v4 Theorem 1.1), `kyle_unique_equilibrium`,
`kyle_existsUnique_equilibrium`, `isEquilibrium_eq_kyleStrategy`,
`isGammaSolution_zero_iff` (v4 Theorem 7.1), `existsUnique_zeroSolution`,
`gamma_eq_half` (v4 Proposition 6.1). They were moved there from
`Statement.lean` in Session 3 Wave 3 because the import DAG forced it —
`Statement.lean` sits below every Session-3 module.

| Module | LOC | Role | Blueprint nodes |
|---|---:|---|---|
| `KyleUniqueness.lean` (root) | 18 | umbrella import | — |
| `Basic.lean` | 64 | scaffolding | — |
| `GaussianHelpers.lean` | 506 | `ϱ` toolkit, tail FTC, null-singleton glue | Tier 0.1 |
| `CondExpBridge.lean` | 912 | explicit Bayes quotient ↔ `condExp` bridge, affine consumers | P1 |
| `Definitions.lean` | 343 | model, order flow, pricing rule, equilibrium pair, `Γ`, `stdModel` | N0 |
| `Statement.lean` | 1466 | Lemmas 2.1–2.3 layer, Prop 4.1, affine regression, `equilibrium_iff_zeroSolution` | A1, A2, A3, R1, N1, Q1, Q2 |
| `Regularity.lean` | 412 | `F ∈ C¹`, eq. (2.3) | R2 |
| `SteinInequality.lean` | 919 | one-sided Gaussian inequality; **zero project imports** | I1, I2, I3 |
| `PosteriorDeriv.lean` | 183 | differentiation-under-the-integral legs for `n`, `p`, `P` | D1 (C¹ legs) |
| `ValueFunction.lean` | 391 | **Session 3** — v4 Lemma 2.4: `insiderProfit` (= Π), FOC, (2.4)–(2.6), (A.1) | B1, B2 |
| `Posterior.lean` | 865 | **Session 3** — v4 Lemma 2.1 joint density, §2.2 `π_y`, Lemma 2.5 (2.7)–(2.8) | A1b, D1-rest, D2 |
| `Resampling.lean` | 970 | **Session 3** — v4 Lemma 2.6 (i)–(iv), Lemma 2.3 tower clause | E1, R2b |
| `Loss.lean` | 283 | **Session 3** — v4 Lemmas 3.1/3.2: `Γ = E[F′(φ(V))]`, definiens agreement | Lemma 3.1/3.2 |
| `Accounting.lean` | 826 | **Session 3** — v4 Prop 5.1 accounting identity (full v4 route) | E2 |
| `SignedRoot.lean` | 536 | **Session 3** — the signed-root construction inside v4 Prop 6.1; `1 ≤ 2Γ` | H1, J1 |
| `Main.lean` | 606 | **Session 3** — v4 Prop 6.1, Theorem 7.1, §7 location–scale, Theorem 1.1 | T3, N2, O1 |
| `AxiomAudit.lean` | 591 | `#print axioms` harness, 399 lines, runs at every build | — |
| `BeyondPaper.lean` | 152 | v2-legacy cubic/`β_γ` layer, fenced as our own extension | (off-DAG) |
| `IdentityTheoremSpike.lean` | 77 | legacy spike; v3 deleted its consumer | (off-DAG) |

Two helper declarations were renamed at closeout and appear under their new
names throughout these documents: `integral_insiderProfit_id_of_closedForm`
(`SignedRoot.lean`, formerly `integral_insiderProfit_id'`) and
`monotone_eq_of_ae_eq_continuous` (`Main.lean`, formerly
`Monotone.eq_of_ae_eq_continuous`, which wrongly suggested a root-namespace
Mathlib lemma).

---

## 1. v3 ↔ v4 crosswalk

The Lean tree and these notes are keyed to **v4**. Older documents in this
repository (`CANARY_REPORT.md`, `RECONCILIATION_REPORT.md`,
`V3_RECONCILIATION_PLAN.md`, `blueprint/*`) are v3-keyed and marked historical.
Full map with per-file impact: `V4_DELTA_REPORT_2026-09-16.md` §1 and §6.

### Results

| v3 | v4 | Lean carrier | Note |
|---|---|---|---|
| Theorem 1 | **Theorem 1.1** | `kyle_equilibrium_pair_iff` (`Main.lean`) | unchanged mathematically |
| Proposition 2 | **Proposition 4.1** | `noiseTraderLoss_le_half`, `noiseTraderLoss_eq_half_iff`, `_eq_neg_half_iff` (`Statement.lean`) | moved §3 → §4 |
| Theorem 3 | **Proposition 6.1** | `gamma_eq_half` (`Main.lean`) | demoted Theorem → Proposition |
| Theorem 4 | **Theorem 7.1** | `isGammaSolution_zero_iff` (`Main.lean`) | moved §3.1 → §7 |
| Lemma 2.1 | **Lemma 2.1** | `map_value_orderFlow`, `lemma21_flowDensity_pos` | the only number *and* statement that survives |
| Lemma 2.2 | **Lemma 2.2** | `lemma21_isPricingRule`, `lemma21_continuous`, `lemma22_memLp_two`, `posterior` | |
| Lemma 2.3 | **Lemma 2.3** | `lemma23_integrable`, `hasDerivAt_gaussianSmoothing`, `gaussianSmoothing_comp_ae_eq_condExp_condExp` | |
| Lemma 2.6 (FOC / `W`) | **Lemma 2.4** | `firstOrderCondition`, `insiderProfit_eq_sq_mul_deriv`, `ae_hasDerivAt_insiderProfit` | v3's divergence clause (12) is **gone** in v4 |
| Lemma 4.1 (posterior) | **Lemma 2.5** | `deriv_inverseRegression_eq_cov`, `deriv_inverseRegression_pos` | |
| Lemma 2.4 (resampling) | **Lemma 2.6** | `resamplingMeasure` + clauses (i)–(iv) | clauses verbatim |
| Lemma 2.5 (one-sided Stein) | **DELETED** | `one_le_sqrt_integral_sq_mul_integral_inv_sq` (`SteinInequality.lean`) | v4 Lemma 2.7 is *Cacoullos*, a different lemma with no Lean counterpart — see **F1** |
| — | **Lemma 2.7** (Cacoullos) | none | new in v4 |
| Lemma 2.7 (a.e. → pointwise) | **Appendix B, Lemma B.1** | none | different statement; see **F11** |
| Proposition 5 | **Prop 5.1 + Lemma 3.1** | `accounting_identity`; `noiseTraderLoss_eq_integral_deriv` | v3's single proposition splits |
| — | **Lemma 3.2** | `insiderProfit_apply`, `measurable_insiderProfit` | new in v4 |
| Proposition 6 (signed root) | unnumbered, inside **Prop 6.1** | `criticalPoint`, `posteriorSlope`, `signedRoot`, `rootSlope` | v4 sets `c := F(0)` |
| Lemma B.1 (complex-analytic scope) | **DELETED** | — | v4's Appendix B is a different appendix |

### Equations

| v3 | v4 | | v3 | v4 |
|---|---|---|---|---|
| (1) | (1.1) | | (11) | (2.6) |
| (2) | (1.2) | | (14) | (4.1) |
| (3) | (2.1) | | (20) | (2.7) |
| (4) | (2.2) | | (21) | (2.8) |
| (5) | (2.3) | | (29) | (A.1) |
| (9) | (2.4) | | (6), (8), (13), (15)–(19), (22)–(28) | unnumbered or gone |
| (10) | (2.5) | | | |

---

## 2. Paper-object → Lean-object map (v4)

### §1 — general model and Theorem 1.1

| Paper object | v4 ref | Lean object |
|---|---|---|
| Probability space; `V ~ N(μ,τ²)`, `U ~ N(0,σ²)` independent, `τ,σ>0` | §1 ¶1 | `structure KyleModel` (paper's prior mean `μ` is `μ₀`) |
| Borel strategy `φ` | §1 | `φ : ℝ → ℝ` + `Measurable φ` (Mathlib `Measurable` on `ℝ` **is** Borel) |
| Order flow `Y_φ = φ(V) + U` | §1 | `KyleModel.orderFlow`; `KyleModel.flowSigma` for `σ(Y_φ)` |
| Competitive pricing: Borel `P` with `P(Y_φ) = E[V∣Y_φ]` a.s. | §1 | `KyleModel.IsPricingRule` (via Mathlib `condExp`) |
| Expected profit `E[(v − P(x+U))x]` | §1 | `KyleModel.expectedProfit` (Bochner) |
| Equilibrium pair `(φ,P)` | §1 | `KyleModel.IsEquilibrium` = `Measurable φ ∧ IsPricingRule φ P ∧ ∀ v x, expectedProfit P v x ≤ expectedProfit P v (φ v)` |
| Kyle's strategy `φ(v) = (σ/τ)(v−μ)`; `λ = τ/(2σ)` | (1.1), (1.2) | `KyleModel.kyleStrategy`, `priceImpact`, `kylePricingRule` |
| **Theorem 1.1** | §1 | `kyle_equilibrium_pair_iff`; projections `kyle_unique_equilibrium`, `kyle_existsUnique_equilibrium`; halves `isEquilibrium_eq_kyleStrategy`, `kyleStrategy_isEquilibrium`, `kyleStrategy_kylePricingRule_isEquilibrium`; rigidity of (1.2) `pricingRule_ae_eq_kylePricingRule`, `eq_kylePricingRule_of_continuous` |

### §2 — normalised model and the regularity layer

| Paper object | v4 ref | Lean object |
|---|---|---|
| `ϱ` standard normal density; normalised model | §2 | `stdNormalPDF`; `stdModel` (all fields proved) |
| Joint density `ϱ(v)ϱ(y−φv)`; `p(y) > 0` | Lemma 2.1 | `jointDensity`, `map_value_orderFlow`; `flowDensity`, `lemma21_flowDensity_pos`, `KyleModel.map_orderFlow`, `KyleModel.flowPDF_pos` |
| `P` the Bayes quotient; continuous; `P(Y)=E[V∣Y] ∈ L²`; `π_y` | Lemma 2.2, §2.2 | `inverseRegression`; `lemma21_continuous`, `lemma21_isPricingRule`, `lemma22_memLp_two`, `lemma21_unique_continuous_version`; `posterior`, `isProbabilityMeasure_posterior`, `inverseRegression_eq_integral_posterior` |
| `F(x) = E[P(x+U)]` finite, `C¹`, (2.1)–(2.3); tower clause | Lemma 2.3 | `gaussianSmoothing`; `integrable_inverseRegression_const_add`, `lemma23_integrable`, `hasDerivAt_gaussianSmoothing`, `continuous_deriv_gaussianSmoothing`, `gaussianSmoothing_eq_convolution`, `deriv_gaussianSmoothing(_eq_integral)`, `gaussianSmoothing_comp_ae_eq_condExp_condExp` |
| `W`/Π: real-valued, attained, convex, `W′=φ` a.e., FOC | Lemma 2.4, (2.4)–(2.6), (A.1) | `insiderProfit`, `insiderProfit_eq_iSup`, `firstOrderCondition`, `insiderProfit_eq_sq_mul_deriv`, `ae_hasDerivAt_insiderProfit`, `insiderProfit_sub_eq_intervalIntegral`, `insiderProfit_subgradient`, `convexOn_insiderProfit`, `insiderProfit_nonneg`, `strictMono_of_isGammaSolution`, `monotone_of_isGammaSolution` |
| `id, φ ∈ L²(π_y)`; `P′ = Cov_{π_y}(id,φ) > 0`; `F′ > 0` | Lemma 2.5, (2.7), (2.8) | `memLp_id_posterior`, `memLp_strategy_posterior`, `deriv_inverseRegression_eq_cov`, `deriv_inverseRegression_pos`, `deriv_gaussianSmoothing_pos(_of_strictMono)`, `strictMono_inverseRegression`, `strictMono_gaussianSmoothing` |
| Conditional resampling, clauses (i)–(iv) | Lemma 2.6 | `resamplingMeasure`, `isProbabilityMeasure_resamplingMeasure`, `resamplingMeasure_map_swap`, `_map_fst`, `_map_snd`, `_map_v0`, `_map_v1`, `_map_y`, `integral_v1_mul_eq_inverseRegression`, `integral_v1_mul_(comp_)eq_gaussianSmoothing` |
| Cacoullos lower Gaussian variance bound | Lemma 2.7 | **none** — see **F1** |

### §§3–7 — the `Γ` pivot, accounting, saturation, rigidity

| Paper object | v4 ref | Lean object |
|---|---|---|
| `Γ` well defined; `= E[U(P̃(Y)−V)] = Cov(U,E[V∣Y]) = E[F′(φ(V))]` | Lemma 3.1 | `noiseTraderLoss`, `integrable_noiseTraderLoss`, `integral_noise_mul_sub_value_eq_noiseTraderLoss`, `covariance_noise_condExp_eq_noiseTraderLoss`, `noiseTraderLoss_eq_integral_deriv` |
| `Π(v)` finite, Borel, version-independent | Lemma 3.2 | `insiderProfit_apply`, `measurable_insiderProfit`, `expectedProfit_inverseRegression`, `objective_eq_expectedProfit` |
| `\|Γ\| ≤ 1/2`, equality iff `φ = ±v + a` a.e. | Prop 4.1, (4.1) | `noiseTraderLoss_le_half`, `noiseTraderLoss_eq_half_iff`, `noiseTraderLoss_eq_neg_half_iff` |
| Accounting identity `Γ = E[Π(V)]` | Prop 5.1 | `accounting_identity`; replica identity `replica_identity`; truncation `clampAt`, `clamp_increment_bounds`, `tendsto_clamp_replica`, `ae_clamp_insiderProfit`; consumers `integrable_insiderProfit_of_isGammaSolution`, `noiseTraderLoss_eq_integral_insiderProfit` |
| Covariance saturation `Γ = 1/2`; signed root | Prop 6.1 | `gamma_eq_half`; `criticalPoint`, `strategy_criticalPoint`, `posteriorSlope(_pos)`, `noiseTraderLoss_eq_integral_posteriorSlope`, `noiseTraderLoss_pos`, `signedRoot`, `signedRoot_sq`, `ae_hasDerivAt_signedRoot`, `rootSlope`, `inv_rootSlope_sq`, `integral_sq_signedRoot`, `integral_inv_sq_rootSlope`, `one_le_two_mul_noiseTraderLoss` |
| Rigidity: pointwise maximisation iff `φ = id` | Thm 7.1 | `isGammaSolution_zero_iff`, `existsUnique_zeroSolution`, `monotone_eq_of_ae_eq_continuous` |
| Standardisation `V̂ = (V−μ)/τ`, `Û = U/σ` | §7 | `KyleModel.map_std_valueLaw`, `map_std_noiseLaw`, `flowPDF_mul_sigma`, `flowNum_mul_sigma`, `bayesPrice_mul_sigma`, `expectedProfit_bayesPrice` (laws only — see **F12**) |

### Beyond-paper layer (fenced, not claim surface)

`BeyondPaper.lean`: the cubic `γt³+t²+γt = 1`, its root `β_γ ∈ (0,1]`, and
`λ_γ = β_γ/(1+β_γ²)` — proved, axiom-clean, anchored to v2's deleted Theorem
3.2. Our own extension, explicitly excluded from every claim.

---

## 3. Modeling choices (C1–C12)

Unchanged in substance from the statement phase; status updated.

- **C1 — abstract probability space.** Theorem 1.1 is stated for *any*
  `KyleModel Ω`. `stdModel` shows the class is inhabited. **Caveat:** it is the
  *only* inhabitant in the tree — see §6.
- **C2 — `τ, σ : ℝ` with `0 < τ`, `0 < σ`**, variances passed to `gaussianReal`
  as `⟨τ^2, sq_nonneg τ⟩`.
- **C3 — `E[V∣Y_φ]` = Mathlib `condExp` w.r.t. `comap Y`.** Junk-value
  conventions are non-binding (measurable `Y`, probability measure, integrable
  `V`), and this is now positively certified: `KyleModel.integrable_V`,
  `measurable_orderFlow`, and the nonzero oracle chain
  `covariance_noise_condExp_eq_noiseTraderLoss` + `noiseTraderLoss_id = 1/2`.
- **C4 — pair notion primary.** `IsEquilibrium` is the paper's pair; the
  strategy-only `IsEquilibriumStrategy` is proved equal to its `∃P` projection
  (`isEquilibriumStrategy_iff_exists`), so the uniqueness theorem refutes the
  weakest available predicate.
- **C5 — Bochner integral for expected profit.** The junk-value risk is closed:
  `KyleModel.integrable_Q_comp_add`, `integrable_inverseRegression_const_add`,
  `Main.integrable_inverseRegression_shift`, `KyleModel.integrable_bayesPrice_comp`
  prove v4 Lemma 2.3's `L¹` clause for every version that matters.
- **C6 — equilibrium quantifier `∀ v x : ℝ`**, uniqueness as exact function
  equality. The a.e.-maximisation variant is v4 Appendix B and is **not**
  formalized (**F11**).
- **C7 — explicit `inverseRegression`, retired as an apology.** v4 §2.2 itself
  defines `P` by this Bayes quotient; the bridge to `condExp`
  (`lemma21_isPricingRule`) is proved for every Borel `φ`.
- **C8 — `γ`-generalization fenced beyond-paper.** `IsGammaSolution γ` is
  defined for all `γ : ℝ`; only `γ = 0` carries paper content.
- **C9/C10 — `betaGamma` totalization and `(0,1]` bounds** — beyond-paper.
- **C11 — `Γ` via the explicit `P`.** See **F2**: the Lean *definiens* is
  `E[U·P(Y)]`, the paper's second expression, with the paper's own definiens and
  the covariance form proved equal.
- **C12 — version clauses stated for the canonical `P`.** See **F3**.

---

## 4. Mathlib-gap inventory (pin `81a5d257`, tag v4.32.0)

1. **No posterior-density / Bayes-quotient interface for
   `ProbabilityTheory.condDistrib`.** We define `P` explicitly (paper-canonical
   under v4 §2.2) and prove the `condExp` bridge ourselves in
   `CondExpBridge.lean`. Upstreaming candidate. Consequence for fidelity: **F4**.
2. **No Gaussian Stein identity / Stieltjes-vs-a.e.-derivative domination for
   monotone functions.** Built from scratch in `SteinInequality.lean` (869 LOC,
   **zero project imports**) — the cleanest upstreaming candidate in the tree.
3. *Minor:* no ready-made `IndepFun Prod.fst Prod.snd (μ.prod ν)` at this pin;
   proved inline in `stdModel`.
4. `GaussianHelpers.lean` (`ϱ` toolkit, tail FTC, null-singleton glue) is a
   second upstreaming candidate.

---

## 5. Fidelity ledger — the twelve deviations (F1–F12)

This replaces the statement-phase "honest fidelity assessment". It is the
deviation list from the final adversarial audit of 2026-09-16, written out in
full. **None of these is a soundness gap**; all are route choices, wording gaps
on unused clauses, hypotheses the paper carries as standing assumptions, or one
explicit scope exclusion. Anything published must carry them.

| # | Paper result | Lean declaration(s) | Deviation |
|---|---|---|---|
| **F1** | v4 Lemma 2.7 (Cacoullos lower Gaussian variance bound), used for `1 ≤ 2Γ` inside Prop 6.1 | `one_le_sqrt_integral_sq_mul_integral_inv_sq` (`SteinInequality.lean`) → `one_le_two_mul_noiseTraderLoss` (`SignedRoot.lean`) | **The single largest divergence.** v4 Lemma 2.7 has *no* Lean counterpart. The step it serves is proved instead by the **v3** one-sided Stein inequality (Lane-C decision D7). So the formalized proof of v4 Prop 6.1 is v3's proof, not v4's. Publications must say "we formalize the v3 route for this one step", not "we formalize the paper". |
| **F2** | v4 §3.1 *defines* `Γ := E[U(P(Y) − V)]` | `noiseTraderLoss` (`Definitions.lean`); bridges `integral_noise_mul_sub_value_eq_noiseTraderLoss`, `covariance_noise_condExp_eq_noiseTraderLoss` (`Loss.lean`) | Lean *defines* `Γ := E[U·P(Y)]` — the paper's **second** expression, which the paper derives in Lemma 3.1. The paper's literal definiens and its `Cov(U, E[V∣Y])` form are both proved equal inside the artifact. No content lost; the starting point differs. |
| **F3** | v4 Lemma 2.3 (version clause), Lemma 3.1, Lemma 3.2 — each stated "for every Borel version `P̃`" | all rendered for the canonical continuous `inverseRegression`; transfer by `KyleModel.pricingRule_ae_eq_of_flowPDF_pos`, `expectedProfit_congr_ae`, `lemma21_unique_continuous_version`, `equilibrium_iff_zeroSolution` | Real weakening **of wording**: no single Lean lemma reads "`Γ = E[U·P̃(Y)]` for every Borel version". The every-version content is recoverable by composing two proved lemmas, and the transfer machinery *is* used on the headline path — but it is never stated as one lemma. |
| **F4** | v4 Lemma 2.2's clause "`y ↦ π_y` is a version of the conditional law of `V` given `Y=y`" | `posterior`, `isProbabilityMeasure_posterior`, `inverseRegression_eq_integral_posterior`, `memLp_id_posterior`, `memLp_strategy_posterior`, `map_value_orderFlow` | Not formalized as such: `ProbabilityTheory.condDistrib` appears nowhere in the tree except two explanatory docstrings (documented Mathlib gap, §4.1). Only the consequences actually used are proved. |
| **F5** | v4 Lemma 2.5: "`P` is **continuously** differentiable" | `hasDerivAt_inverseRegression`, `deriv_inverseRegression_eq_cov`, `deriv_inverseRegression_pos` | Differentiability everywhere, the covariance formula (2.7) and strict positivity are proved; **continuity of `P′` is never stated**. Nothing downstream consumes it. (The corresponding `C¹` clause for `F` *is* fully rendered: `continuous_deriv_gaussianSmoothing`.) |
| **F6** | v4 Lemma 2.6: `V⁽¹⁾` built on an *extension* of the space by Kallenberg's transfer theorem; `V⁽⁰⁾, V⁽¹⁾` conditionally i.i.d. given `Y` | `resamplingMeasure` (explicit `Measure (ℝ×ℝ×ℝ)` by one flat `withDensity`); clauses `resamplingMeasure_map_swap`, `_map_fst`/`_map_snd`, `integral_v1_mul_eq_inverseRegression`, `integral_v1_mul_(comp_)eq_gaussianSmoothing` | Deliberate construction difference (Lane-C decision D4). Conditional i.i.d.-ness is never stated; clauses (iii)/(iv) are in **bounded-test-function** form rather than as `condExp` equalities. Given `integrable_v1_resampling` the two are equivalent, so nothing downstream weakens. |
| **F7** | v4 Lemma 2.4 works with `W(v) := sup_x x(v − F(x))`, allows `+∞`, and proves nonnegativity/convexity *before* assuming pointwise maximisation | `insiderProfit φ v := φ v * (v − F(φ v))` (attained value); bridge `insiderProfit_eq_iSup` | Deliberate (decision D2). "`W` is real-valued" holds by construction rather than being proved of the sup. Corollary: `insiderProfit_nonneg` and `convexOn_insiderProfit` carry the hypothesis `IsGammaSolution 0 φ`, where the paper has them for arbitrary `φ`. Every consumer supplies that hypothesis. |
| **F8** | v4 Theorem 1.1 | `kyle_equilibrium_pair_iff` | Carries an explicit `(hP : Measurable P)` that the paper folds into its standing sentence "`P : ℝ → ℝ` is a Borel-measurable pricing rule". Genuinely needed for the `←` direction; redundant for `→`. Faithful, but a reader comparing lines sees one extra hypothesis. |
| **F9** | v4 Prop 5.1 hypothesises only "`φ` nondecreasing and `Π(V) ≥ 0` a.s." | `accounting_identity` | Carries a redundant `Measurable φ` alongside `Monotone φ` (a monotone `ℝ → ℝ` is automatically Borel). Harmless and always available at call sites, but formally weaker than the paper. |
| **F10** | v4 Prop 6.1 and Thm 7.1 hypothesise "`(φ,P)` is an equilibrium in the normalised model" | `gamma_eq_half`, `isGammaSolution_zero_iff` | **Lean is stronger.** Both assume only `IsGammaSolution 0 φ` (pointwise maximisation against the canonical `F`) — the first line of the paper's own proof, strictly weaker than equilibrium, with `equilibrium_iff_zeroSolution` bridging. No loss. |
| **F11** | v4 **Appendix B** — a.e. maximisation ⇒ pointwise; equilibrium strategy unique modulo null sets (the footnote-1 variant) | **none** | **Scope exclusion**, explicitly deferred (blueprint node R3). Every claim must scope Theorem 1.1 to the **pointwise**-maximisation definition. |
| **F12** | v4 §7 standardises the probability space (`V̂ := (V−μ)/τ`, `Û := U/σ`) and asserts the equilibrium-transfer biconditional | `KyleModel.map_std_valueLaw`, `map_std_noiseLaw`, `flowPDF_mul_sigma`, `flowNum_mul_sigma`, `bayesPrice_mul_sigma`, `expectedProfit_bayesPrice` | Lean never builds the standardised `KyleModel`; it standardises the **laws** and pushes §7 through two Bochner integrals. The §7 biconditional is never stated — only the direction the headline needs. Documented in `Main.lean`'s "Route taken" block. |

**Non-vacuity, positively certified.** Every hypothesis class is proved
inhabited and every bound witnessed tight: `isGammaSolution_zero_id`,
`kyleStrategy_kylePricingRule_isEquilibrium` (for every `M`),
`stdModel_kyleStrategy = id`, and the oracle chain `inverseRegression_id`,
`gaussianSmoothing_id`, `insiderProfit_id`, `noiseTraderLoss_id = 1/2`,
`integral_insiderProfit_id` / `integral_insiderProfit_id_of_closedForm` (two
independent routes to the same number), `two_mul_noiseTraderLoss_id`,
`one_le_two_mul_noiseTraderLoss_id`. `isGammaSolution_zero_iff` and
`kyle_unique_equilibrium` pin the solution set to a singleton, so the predicates
are non-trivial in both directions.

---

## 6. What is **not** formalized

Stated plainly, because these are what a reviewer will ask about.

1. **v4 Appendix B** — the a.e.-maximisation / quasi-equilibrium variant (F11).
2. **`π_y` as a `condDistrib`** — the conditional-law clause of Lemma 2.2 (F4).
3. **Continuity of `P′`** — differentiability, the formula and positivity are
   proved; the `C¹` wording for `P` is not (F5).
4. **Conditional i.i.d.-ness of the resampled pair**, and Kallenberg's transfer
   theorem (F6).
5. **The §7 equilibrium-transfer biconditional** (F12).
6. **A general-parameter `KyleModel` inhabitant.** The tree constructs exactly
   one: `stdModel` (`μ₀ = 0, τ = σ = 1`). Every headline theorem is universally
   quantified over `M : KyleModel Ω`, so none can be false — but the artifact
   never certifies that a `KyleModel` exists at, say, `μ₀ = 3, τ = 2, σ = 5`,
   and therefore never exhibits Kyle's `λ = τ/(2σ)` at a value other than `1/2`.
   This is the one genuine vacuity-adjacent gap; the fix is ~20 lines mirroring
   `stdModel` (`generalModel` on `(gaussianReal μ₀ ⟨τ²,_⟩).prod (gaussianReal 0
   ⟨σ²,_⟩)`), recommended before any external step. **Out of scope for the
   documents closeout — it is a Lean change.**
7. Cacoullos's lower Gaussian variance bound (v4 Lemma 2.7) — replaced by the v3
   Stein route (F1).

---

## 7. Reproduction

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin/kyle-formalization
lake build          # green: 0 errors, 0 warnings, 0 sorries
```

From scratch (project oleans only — never touch `.lake/packages`):

```bash
rm -rf .lake/build/lib/lean/KyleUniqueness .lake/build/lib/lean/KyleUniqueness.{olean,olean.hash,ilean,ilean.hash,trace}
lake build                                                        # 3149 jobs
lake build 2>&1 | grep -c "declaration uses"                      # 0
lake build 2>&1 | grep -o "depends on axioms: \[.*\]" | sort -u    # exactly one line
```

The axiom audit is `KyleUniqueness/AxiomAudit.lean` and runs as part of the
build. Its coverage is **exhaustive over public named declarations**: 399 of
399. Every column-0 non-`private` named declaration across the 17 source
modules was enumerated and matched against the 399 audited names — 0 missing,
0 extra. The only omissions are the four anonymous `instance`s
(`Definitions.lean:111`, `GaussianHelpers.lean:81`, `CondExpBridge.lean:110`
and `:113`), which have machine-generated names and cannot be cited by hand,
exactly as the module docstring states. Tree-wide axiom-cleanliness is
corroborated by the build itself (zero `declaration uses 'sorry'` on a
from-source rebuild plus zero unsafe constructs).

Note that the three `lake build 2>&1 | grep ...` lines above only produce
output on the *first* build after step 1: a second invocation is fully cached
and prints nothing, which is not the audit vanishing. Re-run step 1 to see the
axiom lines again.

---

## 8. Document history

| Date | Event |
|---|---|
| 2026-08-11/12 | statement phase against v2, then the v2 → v3 reconciliation (`V3_RECONCILIATION_PLAN.md`, `RECONCILIATION_REPORT.md`, `CANARY_REPORT.md` — all now historical) |
| 2026-08-12 | Session 1: Tier 1 + R1 + Q2 + the `σ=τ=1` bridge; 14 sorries → 2 |
| 2026-08-18 | Session 2: Stein pipeline (I1–I3), R2, D1 `C¹` legs |
| 2026-09-16 | v4 found and reconciled (`V4_DELTA_REPORT_2026-09-16.md`); Lane-C decisions D1–D9 (`blueprint/LANE_C_DECISIONS_2026-09-16.md`) |
| 2026-09-16 | Session 3, Waves 1–3: seven new modules, campaign closed at **0 sorries**, commit `f975dbc` |
| 2026-09-16 | documents closeout: this file re-keyed to v4, F1–F12 ledger installed |
