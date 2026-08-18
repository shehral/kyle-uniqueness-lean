# STATEMENT_NOTES — Monteiro–Tourky Kyle-uniqueness, formal statement phase

Paper: Monteiro & Tourky, *The one-period Gaussian Kyle model has exactly
one equilibrium*, arXiv:2607.23585 **v3** (2026-08-10). All §/eq./lemma
numbers below are **v3's** unless marked "v2". (The project was originally
stated against v2, whose title was *Monotonicity and Rigidity in Gaussian
Inverse Regression: …*; v3 is a rewrite of the proof architecture under the
new title. The v2 → v3 reconciliation was executed 2026-08-12 per
`V3_RECONCILIATION_PLAN.md`; the full statement-level diff lives there, and
`RECONCILIATION_REPORT.md` records what changed in the Lean tree.)

Artifact: `KyleUniqueness/Definitions.lean` + `KyleUniqueness/Statement.lean`
(+ `KyleUniqueness/BeyondPaper.lean`, `KyleUniqueness/AxiomAudit.lean`,
proof infrastructure in `GaussianHelpers.lean` / `CondExpBridge.lean`),
Lean `v4.32.0`, Mathlib `81a5d257` (tag v4.32.0, byte-identical to
formal-mathfin's pin).

Build status (2026-08-12, post-reconciliation + Tier-1/2 proving session —
see `PROVING_LOG.md`): **`lake build` green** — 0 errors, 0 non-`sorry`
warnings, **2 `sorry`s**, both in `Statement.lean` and both headline
uniqueness carriers (`isGammaSolution_zero_iff` rigidity direction,
`isEquilibrium_eq_kyleStrategy`); none in any definition. Axiom audit
(`KyleUniqueness/AxiomAudit.lean`, runs at every build): every proved
declaration — including both canaries, all infrastructure, Lemmas 2.1–2.3,
Proposition 2 in full, and the affine-regression layer — depends only on
`[propext, Classical.choice, Quot.sound]`; the two open carriers (and the
assembled statements inheriting through them) additionally on `sorryAx`,
as expected. **Local only — nothing published.**

---

## 1. Paper-object → Lean-object map (v3 numbering)

### The general model and Theorem 1 (§1)

| Paper object | Paper ref (v3) | Lean object | Notes |
|---|---|---|---|
| Probability space; `V ~ N(μ,τ²)`, `U ~ N(0,σ²)` indep., `τ,σ>0` | §1 ¶1 | `structure KyleModel` (fields `μ hprob μ₀ τ σ hτ hσ V U hV hU hVlaw hUlaw hIndep`) | abstract `(Ω, m, μ)`; laws via `Measure.map _ = gaussianReal _ _`; paper's prior mean `μ` renamed `μ₀` |
| Borel strategy `φ : ℝ → ℝ` | §1 | `φ : ℝ → ℝ` + `Measurable φ` | Mathlib `Measurable` on `ℝ` **is** Borel — no gap |
| Order flow `Y_φ = φ(V) + U` | §1 | `KyleModel.orderFlow` | |
| Market makers' information `σ(Y_φ)` | implicit in `E[V∣Y_φ]` | `KyleModel.flowSigma` (`MeasurableSpace.comap`) | |
| Competitive pricing (equilibrium def, item 2): Borel `P` with `P(Y_φ) = E[V∣Y_φ]` a.s. | §1 | `KyleModel.IsPricingRule` (fields `measurable`, `ae_eq_condExp` via `MeasureTheory.condExp`) | see choice C3; now *exactly* the paper's pair-component |
| Expected profit `E[(v − P(x+U))x]` | §1, profit-max condition | `KyleModel.expectedProfit` (Bochner `∫ ω, … ∂μ`) | see choice C5 — caveat now discharged by v3 Lemmas 2.2/2.3 as stated paper content |
| **Equilibrium pair `(φ, P)`** (items 1+2) | §1, Theorem 1 | `KyleModel.IsEquilibrium` (structure: `measurable`, `pricingRule`, `isMaxOn`) | **v3's primary notion**; `∀ v x` pointwise, exactly the paper |
| Equilibrium strategy (∃-projection) | derived (v2's primary notion) | `KyleModel.IsEquilibriumStrategy`; glue `IsEquilibrium.isEquilibriumStrategy`, `isEquilibriumStrategy_iff_exists` (proved) | see choice C4 |
| Kyle's affine strategy `φ(v) = (σ/τ)(v−μ)` | eq. **(1)** | `KyleModel.kyleStrategy` | v2 eq. (2) |
| Price impact `λ = τ/(2σ)`; `P(Y_φ) = μ + λY_φ` a.s. | eq. **(2)** | `KyleModel.priceImpact`, `KyleModel.kylePricingRule` | v2 eq. (3); v3 states it a.s., "continuous version" language dropped |
| **Theorem 1** (pair iff) | §1 | `kyle_equilibrium_pair_iff` — assembled from `kyleStrategy_isEquilibrium` (proved), `isEquilibrium_eq_kyleStrategy` (sorried), `isPricingRule_kylePricingRule` (proved), `pricingRule_ae_orderFlow` (proved), `pricingRule_ae_eq_kylePricingRule` (sorried), `expectedProfit_congr_ae` (proved) — no `sorry` of its own | the strengthened v3 headline |
| Theorem 1, strategy projections | §1 | `kyle_unique_equilibrium` (iff), `kyle_existsUnique_equilibrium` (`∃!`) — assembled, no own `sorry` | |
| `(1)∧(2) ⇒` equilibrium (converse leg, pair form) | Theorem 1 | `kyleStrategy_kylePricingRule_isEquilibrium` — **proved** | v3 supplies the textual proof v2 only asserted |
| Pricing-rule uniqueness, a.e. form | Theorem 1 eq. (2) + intro remark | `pricingRule_ae_eq_kylePricingRule` (sorried, primary); corollary `eq_kylePricingRule_of_continuous` (derived, no own `sorry`) | v2's "only continuous version" kept as corollary |
| Version-independence of profits | Lemmas 2.2/2.3 (promoted from v2 remark) | `expectedProfit_congr_ae` — **proved**; `pricingRule_ae_orderFlow` — **proved** | |

### The normalised model (§2), Proposition 2, Theorems 3–4

| Paper object | Paper ref (v3) | Lean object | Notes |
|---|---|---|---|
| `ϱ` standard normal density | §2 | `stdNormalPDF := gaussianPDFReal 0 1` | `(√(2π))⁻¹ e^{−x²/2}` definitionally |
| Normalised model (`V,U` std normal) | §2 | `stdModel : KyleModel (ℝ × ℝ)` — coordinates under `(gaussianReal 0 1).prod (gaussianReal 0 1)` | all fields **proved** (no sorry) |
| `p(y) = E[ϱ(y−φ(V))]`, everywhere positive | Lemma 2.1 | `flowDensity`; `lemma21_flowDensity_pos` — **proved** | also discharges the `/0` convention, C7 |
| `P` := explicit Bayes quotient (posterior mean) | **§2.2 display** + eq. (6) | `inverseRegression` | **v3 defines `P` by our exact closed form** — the v2 MATHLIB-GAP workaround is now paper-canonical (C7 retired) |
| Lemma 2.2: `P` continuous, `P(Y) = E[V∣Y] ∈ L²` a.s. | Lemma 2.2 | `lemma21_isPricingRule` — **proved (canary)**; `lemma21_continuous` (sorried); `lemma22_memLp_two` (sorried) | |
| Lemma 2.3: `P̃(x+U) ∈ L¹` every Borel version; `F ∈ C¹`, eqs. (3)–(5) | Lemma 2.3 | `gaussianSmoothing` (`F`); `lemma23_integrable` (sorried) | replaces v2's growth bound eq. (4) (deleted from the paper); the `C¹` + `F′` formula enter the blueprint as proof obligations (node R2), not claim surface |
| `W(v) = sup_x x(v − F(x))`; condition (17) | eqs. (8), (17) | `objective 0`, `IsGammaSolution 0` | the `γ ≠ 0` readings of the same defs are beyond-paper v2 legacy (see `BeyondPaper.lean` header) |
| **Γ = Cov(U, E[V∣Y])** noise traders' loss | eq. **(13)** | `noiseTraderLoss` (= `E[U·P(Y)]` via the explicit `P`; identification with the covariance = Lemma 2.2 + `E U = 0`) | the organising quantity of v3's proof |
| **Proposition 2**: Γ finite; `−1/2 ≤ Γ ≤ 1/2` (14); `Γ = ±1/2 ⟺ φ = ±v + a` a.e. (15) | Prop 2 | `integrable_noiseTraderLoss`, `noiseTraderLoss_le_half`, `noiseTraderLoss_eq_half_iff`, `noiseTraderLoss_eq_neg_half_iff` (all sorried) | stated for EVERY Borel `φ`, exactly as the paper |
| **Theorem 4**: condition (17) ⟺ `φ = id` | Thm 4, eq. (19) | `isGammaSolution_zero_iff` (sorried — the primary rigidity obligation); `existsUnique_zeroSolution` assembled | v2's Corollary 3.3, promoted; the general-γ classification it was derived from is gone from the paper and from our claim surface |
| Affine-strategy Gaussian regression (Thm 4/Thm 1 proofs) | §3.1 / Thm 4 proof | `inverseRegression_affine`, `gaussianSmoothing_affine` (sorried); `_id` forms derived | specialises v2's deleted `λ_γ` formulas to the only case v3 uses |
| Location–scale standardisation | proof of Thm 1, §3.1 | `equilibrium_iff_zeroSolution` (the `σ=τ=1` instance, sorried) + `stdModel_kyleStrategy` (proved) | v2 §3.2, same computation |
| Theorem 3 (`(17) ⇒ Γ = 1/2`), Prop 5, Prop 6, Lemmas 2.4–2.7 | §§2–4 | not stated (proof-phase machinery) | enter via `blueprint/blueprint.md` as proof obligations of the statements above |

### Beyond-paper layer (v2 legacy, fenced)

| Object | Origin | Lean | Status |
|---|---|---|---|
| cubic `γt³+t²+γt = 1`, root `β_γ ∈ (0,1]`, `λ_γ = β_γ/(1+β_γ²)` | v2 Thm 3.2 (deleted in v3) | `BeyondPaper.lean`: `cubic_*`, `betaGamma` + 5 spec lemmas, `lambdaGamma`, `lambdaGamma_zero` | **all proved**, axiom-clean; labelled beyond-paper — our own extension, not v3 content |

### v2 → v3 statement/equation renumber table (for reading old docs)

| v2 | v3 | | v2 eq. | v3 eq. |
|---|---|---|---|---|
| Theorem 1.1 | Theorem 1 (strengthened to pair-iff) | | (2) strategy | (1) |
| Lemma 2.1 (p, P, growth, analytic F) | Lemmas 2.1 + 2.2 + 2.3 (growth bound deleted; `C¹` only) | | (3) pricing rule | (2) |
| Definition 2.2 (γ-solutions) | eq. (8) + condition (17), γ = 0 only | | (4) growth bound | — deleted |
| Lemma 2.3 (FOC) | Lemma 2.6, eqs. (9)–(12) | | (5) F′ formula | (5) |
| Proposition 2.4 (A, B, e, R) | — replaced by Prop 2 (Γ) + Thm 3 | | (7) FOC | (9) |
| Theorem 3.1 (Euler identity) | — deleted (F-linearity via joint Gaussianity in Thm 4's proof) | | (10) posterior mean | (6) |
| Theorem 3.2 (γ-classification, cubic) | — deleted (γ = 0 shadow only) | | (14) `E[V₁∣V₀]` | Lemma 2.4(iv) |
| Corollary 3.3 | **Theorem 4** (promoted) | | (19) e | (22) (e renamed Γ) |
| Lemma 4.1 (AB ≤ 1) | — replaced by Prop 2 | | (27)–(29) signed root | (10), (26)–(28) |
| Lemma 4.2 (posterior diff.) | Lemma 4.1, eqs. (20)–(21) | | (31) Gaussian ineq. | (7) |
| Lemmas 4.3/4.4 (balance/channel) | Lemma 2.4 + Prop 5, eqs. (22)–(24) | | | |
| Lemma 5.1–5.3 (pincer + Stein) | Thm 3 + Prop 6 + Lemma 2.5 | | | |
| Remark 5.4 (γ < 0 bifurcation) | — deleted | | | |

Full node-level detail: `V3_RECONCILIATION_PLAN.md` §1.3–1.4.

## 2. Modeling choices (each a fidelity decision)

- **C1 — abstract probability space.** Theorem 1 is stated for *any*
  `KyleModel Ω`: any probability space carrying independent `V ~ N(μ₀,τ²)`,
  `U ~ N(0,σ²)`. Exactly the paper's distribution-level model. (`stdModel`
  shows the class is inhabited, so the statements are not vacuous.)
- **C2 — `τ, σ : ℝ` with `0 < τ`, `0 < σ`;** variances passed to
  `gaussianReal` as `⟨τ^2, sq_nonneg τ⟩ : ℝ≥0`. Mirrors the paper's
  standard deviations exactly.
- **C3 — `E[V∣Y_φ]` = Mathlib `condExp` w.r.t. `comap Y`.** Junk-value
  conventions of `condExp` are all non-binding here (measurable `Y`,
  probability measure, integrable `V`), so the Lean condition is the
  paper's condition on the nose. **Certified non-vacuous by the proved
  canaries** (`lemma21_isPricingRule`, `isPricingRule_kylePricingRule`).
- **C4 — pair notion primary; `∃ P`-projection retained.** v3's equilibrium
  is the pair `(φ, P)` — formalized verbatim as `KyleModel.IsEquilibrium`
  and characterised by `kyle_equilibrium_pair_iff`. The strategy-only
  `IsEquilibriumStrategy` (v2's reading, `∃`-quantified over pricing rules)
  is kept and PROVED equivalent to `∃ P, IsEquilibrium φ P`
  (`isEquilibriumStrategy_iff_exists`); the `∃`-quantifier makes the
  strategy-uniqueness statement strongest. What v2 justified by a remark
  (version-independence) is now partly *proved* (`pricingRule_ae_orderFlow`,
  `expectedProfit_congr_ae`) and partly stated paper content (Lemmas
  2.2/2.3 → `lemma23_integrable`).
- **C5 — Bochner integral for expected profit.** `expectedProfit` is junk
  (0) for non-integrable integrands. v3 Lemmas 2.2 and 2.3 now *state as
  paper lemmas* that expected profits are finite and version-independent
  for every Borel pricing-rule version — the reading of the definition no
  longer leans on an unpromoted remark. The integrability leg is tracked as
  `lemma23_integrable`; the version-independence leg is already proved
  (`expectedProfit_congr_ae`). Canary logic unchanged: a wrong definition
  here would have made `kyleStrategy_isEquilibrium` unprovable; it is
  proved.
- **C6 — equilibrium quantifier `∀ v x : ℝ`** — pointwise optimality at
  every `v`, uniqueness as exact function equality `φ = M.kyleStrategy`.
  Matches v3's primary definition (v3's a.e.-maximisation variant, Lemma
  2.7, is deliberately NOT yet stated — deferred bonus content).
- **C7 — explicit `inverseRegression` — RETIRED as an apology.** v2 called
  `P` "the unique continuous version of `y ↦ E[V∣Y=y]`" (no Mathlib API —
  the original GAP-1) and we defined it by the closed-form Bayes quotient
  as a workaround. **v3 §2.2 now *defines* `P` by exactly this closed
  form**, so the modeling choice is paper-canonical, and the bridge to
  `condExp` (`lemma21_isPricingRule` = v3 Lemma 2.2) is **proved**. What
  remains of GAP-1 is only an upstreaming opportunity, not a fidelity
  liability.
- **C8 — `γ`-generalization fenced beyond-paper.** The quadratic-cost
  family was v2 content and is gone from v3. `objective γ`/`IsGammaSolution
  γ` remain as definitions (their `γ = 0` instance IS the paper's (8)/(17));
  every general-γ *theorem* was deleted from the claim surface, and the
  proved cubic layer moved to `BeyondPaper.lean` with an explicit
  beyond-paper header (v2-legacy extension, ours).
- **C9/C10 — `betaGamma` totalization and `(0,1]` bounds** — unchanged, now
  beyond-paper (see `BeyondPaper.lean`).
- **C11 — `noiseTraderLoss` via the explicit `P` (new).** v3's
  `Γ = Cov(U, E[V∣Y])` is realised as the Bochner integral
  `E[U·P(Y)]` on the canonical space with `P = inverseRegression φ`.
  Identification with the abstract covariance = Lemma 2.2 (canary, proved)
  + `E U = 0`; the junk-value risk of the Bochner integral is de-vacuated
  by the stated `integrable_noiseTraderLoss` (Prop 2's "Γ is finite").
  Proposition 2 is stated for EVERY Borel `φ`, as in the paper.
- **C12 — `lemma23_integrable` stated for the canonical version.** v3
  Lemma 2.3 asserts `P̃(x+U) ∈ L¹` for *every* Borel version `P̃`; we state
  it for the canonical `inverseRegression` (the version the normalised
  layer uses everywhere). The every-version form follows from Lebesgue-a.e.
  agreement of versions + `x+U` having a density — the same mechanism
  already proved in `expectedProfit_congr_ae`.

## 3. MATHLIB-GAP inventory (at pin `81a5d257`, tag v4.32.0)

1. **GAP-1 (downgraded from fidelity-gap to upstream-opportunity):** no
   posterior-density / Bayes-quotient interface for
   `ProbabilityTheory.condDistrib`. v3 defines `P` explicitly, so our
   `flowDensity`/`inverseRegression` + the **proved** bridge
   `lemma21_isPricingRule` now carry the paper's meaning with no residual
   apology. The bridge machinery (`CondExpBridge.lean`) is an upstreaming
   candidate.
2. *Minor:* no ready-made `IndepFun Prod.fst Prod.snd (μ.prod ν)` lemma at
   this pin; proved inline in `stdModel` (3 lines, no gap left).
3. *Noted for the proof phase:* no Gaussian Stein identity /
   Stieltjes-vs-a.e.-derivative domination for monotone functions (v3
   Lemma 2.5 = blueprint I1–I3; already de-fanged by the API audit — see
   `blueprint/mathlib_api_audit.md` §5–6 and the audit corrections
   addendum). The v2-era gaps around entire extensions / real-analyticity
   are **moot**: v3 uses no complex analysis.

Audit corrections from the canary phase (2026-08-12), folded into
`blueprint/mathlib_api_audit.md` §12: `NoAtoms` →
`MeasureTheory.NullSingletonClass` rename (audit §10 item 1 was NOT
missing); `exists_accPt_of_nullSingletonClass` exists at the pin;
`integrable_id_gaussianReal` derived in `GaussianHelpers`.

## 4. Sorry inventory — 2 open obligations (12 of 14 closed 2026-08-12, `PROVING_LOG.md`)

| # | Declaration | v3 ref | Blueprint node | Status (2026-08-12) |
|---|---|---|---|---|
| 1 | `lemma21_continuous` | Lemma 2.2 (continuity) | A2 | **PROVED** (DCT) |
| 2 | `lemma22_memLp_two` | Lemma 2.2 (`P(Y) ∈ L²`) | Q1 input | **PROVED** (`MemLp.condExp` contraction) |
| 3 | `lemma23_integrable` | Lemma 2.3 (`P(x+U) ∈ L¹`) | **R1** | **PROVED** (K_x kernel bound, 3-case) |
| 4 | `lemma21_unique_continuous_version` | auxiliary (v2 legacy) | A3 | **PROVED** (law identity + `Continuous.ae_eq_iff_eq`) |
| 5 | `equilibrium_iff_zeroSolution` | proof of Thm 1, §3.1 | O1 leg | **PROVED** (profit = `x(v−F(x))` for every pricing rule) |
| 6 | `integrable_noiseTraderLoss` | Prop 2 (Γ finite) | **Q1** | **PROVED** (L²·L²) |
| 7 | `noiseTraderLoss_le_half` | Prop 2, eq. (14) | **Q1** | **PROVED** (L² expansion + projection identity) |
| 8 | `noiseTraderLoss_eq_half_iff` | Prop 2, eq. (15), s = +1 | **Q2** | **PROVED** (Tonelli sections + translation invariance) |
| 9 | `noiseTraderLoss_eq_neg_half_iff` | Prop 2, eq. (15), s = −1 | **Q2** | **PROVED** (mirror, via signed private core) |
| 10 | `isGammaSolution_zero_iff` | **Theorem 4** | N2′ | **OPEN** — existence direction proved in-file; rigidity direction needs Theorem 3 (§4 machinery: B/D/E/H/I nodes) |
| 11 | `inverseRegression_affine` | Thm 4/Thm 1 proofs | N1 | **PROVED** (complete-the-square) |
| 12 | `gaussianSmoothing_affine` | same | N1 | **PROVED** |
| 13 | `isEquilibrium_eq_kyleStrategy` | Theorem 1 (⇒, strategy half) | O1 | **OPEN** — location–scale + Theorem 4; blocked on the same §4 machinery |
| 14 | `pricingRule_ae_eq_kylePricingRule` | Theorem 1 eq. (2) (pricing uniqueness) | O1 leg | **PROVED** (order-flow law identity `KyleModel.map_orderFlow`) |

Sorry-free layer (proved): everything above marked PROVED, plus both
canaries (`kyleStrategy_isEquilibrium`, `lemma21_isPricingRule`),
`lemma21_flowDensity_pos`, `isPricingRule_kylePricingRule`,
`kyleStrategy_kylePricingRule_isEquilibrium` (pair-form existence),
`pricingRule_ae_orderFlow`, `expectedProfit_congr_ae`, `stdModel` (all
fields), `stdModel_kyleStrategy`, `IsEquilibrium.isEquilibriumStrategy`,
`isEquilibriumStrategy_iff_exists`, `inverseRegression_id`,
`gaussianSmoothing_id`, `eq_kylePricingRule_of_continuous` (the last three
upgraded to fully-proved when their legs closed), the entire
`GaussianHelpers`/`CondExpBridge` infrastructure (now incl. the order-flow
law identity `KyleModel.map_orderFlow` and the `K_x`
complete-the-square/moment toolkit), the identity-theorem spike, and the
beyond-paper cubic layer.
Assembled-without-own-sorry (inheriting `sorryAx` only through #10/#13):
`kyle_equilibrium_pair_iff`, `kyle_unique_equilibrium`,
`kyle_existsUnique_equilibrium`, `existsUnique_zeroSolution`.

## 5. Honest fidelity assessment

**Does the formal Theorem 1 say what v3's Theorem 1 says?** Yes, with the
following accounting:

- The *model* is faithful at the distribution level (C1–C3), and the
  equilibrium notion is now v3's own pair `(φ, P)` (C4), with pointwise
  profit maximisation at **every** `v` against **all** deviations `x`, and
  strategy-uniqueness as **exact** function equality. The pricing-half
  conclusion is a.s. along the flow, exactly eq. (2)'s phrasing.
- `kyle_equilibrium_pair_iff` is assembled from two sorried legs
  (`isEquilibrium_eq_kyleStrategy`, `pricingRule_ae_eq_kylePricingRule`)
  plus proved glue. Anyone auditing the claim should read it together with
  those two names; the assembly itself adds no assumptions.
- Two places where a statement's *reading* leans on paper lemmas, both
  strictly improved since v2: (i) C5's Bochner-vs-honest expectation now
  matches **stated** paper lemmas (2.2/2.3) rather than a remark, with the
  version-independence half already **proved** and the integrability half
  tracked as `lemma23_integrable`; (ii) `noiseTraderLoss` reads as the
  paper's `Γ` through the proved canary (Lemma 2.2) plus
  `integrable_noiseTraderLoss` (C11). Neither can silently weaken the
  headline: wrong readings would make the proved canaries or the stated
  bridges unprovable, not vacuously provable.
- Theorem 4 and Proposition 2 are faithful **as a package** with the
  `lemma21_*`/`lemma22_*`/`lemma23_*` bridges and
  `equilibrium_iff_zeroSolution`, which jointly assert that the explicit
  `P`/`F`/`Γ` are the paper's objects. We say so here explicitly.
- Known deviations, all conservative: paper's prior mean `μ` renamed `μ₀`;
  `IsGammaSolution` defined for all `γ : ℝ` although only `γ = 0` carries
  any paper-anchored theorem (C8); `betaGamma` layer fenced beyond-paper;
  `stdModel` fixes one canonical normalised space (the paper's §2 does the
  same); Prop 2 stated via the canonical version of `P` (C11/C12). No
  statement quantifies over fewer strategies, fewer models, or weaker
  conclusions than the paper's.
- **Not yet stated** (deliberately, deferred bonus content): v3's
  a.e.-maximisation variant of Theorem 1 (intro remark + Lemma 2.7). It is
  strictly additional robustness; the headline pair-iff does not depend on
  it.
- **Residual risk, stated plainly:** the definitional-fidelity risk that
  dominated the statement phase is now largely *discharged* — both canaries
  are proved, so `IsPricingRule` is satisfiable, `expectedProfit` evaluates
  to the paper's quadratic against the affine rule, and the explicit `P` is
  a genuine pricing rule for every Borel strategy. What remains open is
  exactly the mathematics: the uniqueness legs (#10, #13), the regularity
  layer (#1–#3), Proposition 2 (#6–#9), and the bookkeeping bridges (#5,
  #11, #12, #14). None of these can make the headline vacuously true.

## 6. Reproduction

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin/kyle-formalization
lake build          # green; 2 "declaration uses 'sorry'" warnings, nothing else
```

The axiom audit prints at every build from
`KyleUniqueness/AxiomAudit.lean` (`#print axioms` per public statement):
proved layer → `[propext, Classical.choice, Quot.sound]`; sorried
statements additionally `sorryAx`.

## 7. Next phase (not this deliverable)

Proof milestones per `blueprint/attack_order.md` (v3 revision): R1/R2
regularity → Lemma 2.6 FOC layer → posterior differentiation → Lemma 2.4 +
Prop 5 → Prop 6 + Lemma 2.5 (Stein) → Thm 3 → Q1/Q2 (Prop 2) → Thm 4 →
Thm 1. The two remaining hard blocks are the Stein pipeline (I1–I3) and the
signed root (H1) — both v3-unchanged and both already de-risked by the API
audit. Before any public claim: re-check Lean Zulip for competing Kyle
formalizations (recon found none as of 2026-08-11) and re-verify the arXiv
version (v3 as of 2026-08-12).
