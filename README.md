# KyleUniqueness: the one-period Kyle model has one equilibrium, in Lean 4

[![build](https://github.com/shehral/kyle-uniqueness-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/shehral/kyle-uniqueness-lean/actions)
[![Lean](https://img.shields.io/badge/Lean-4.32.0-blue)](lean-toolchain)
[![sorries](https://img.shields.io/badge/sorries-0-brightgreen)](KyleUniqueness/AxiomAudit.lean)
[![axioms](https://img.shields.io/badge/axioms-propext,_Classical.choice,_Quot.sound-blue)](KyleUniqueness/AxiomAudit.lean)
[![license](https://img.shields.io/badge/license-Apache_2.0-blue)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23912107.svg)](https://doi.org/10.5281/zenodo.23912107)
[![arXiv](https://img.shields.io/badge/source_paper-2607.23585v4-b31b1b)](https://arxiv.org/abs/2607.23585v4)

> A **complete** Lean 4 / Mathlib formalization of **Monteiro & Tourky, *"The
> one-period Kyle model has one equilibrium"* (arXiv:2607.23585v4)**. As far as
> we know, it is the first machine-checked proof of this result and the first
> formalization of any Kyle model. `lake build` is green from scratch with
> **zero `sorry`**, and every audited declaration depends only on `propext`,
> `Classical.choice` and `Quot.sound`.

## What and why

Kyle (1985) is the foundational model of informed trading. An insider who knows
the asset value `V ~ N(μ, τ²)` submits an order, noise traders submit
`U ~ N(0, σ²)`, and competitive market makers price the total order flow at its
conditional expectation. Kyle exhibited the linear equilibrium
`φ(v) = (σ/τ)(v − μ)`. Whether it is the **only** equilibrium, with no
regularity or moment assumption on the strategy, stayed open for four decades:
McLennan, Monteiro and Tourky (2017) got uniqueness only within an
analytically continuable class and left the general case open.

In 2026 Monteiro and Tourky closed it: **every equilibrium is Kyle's affine
equilibrium, and the (strategy, pricing rule) pair is unique.** The proof is
probabilistic and convex-analytic. Its organising quantity is the noise
traders' expected loss `Γ`, which satisfies the sharp bound `|Γ| ≤ 1/2` for
*every* Borel strategy, with equality exactly at affine strategies, while every
equilibrium forces `Γ = 1/2` (via an accounting identity, a conditional
resampling representation, and a Gaussian inequality for monotone functions).
One period and explicit densities mean no Brownian motion and no stochastic
integration: **the formalization needs only Mathlib.**

Why formalize it? The result is recent mathematics that resolves an old
question, and its delicate parts (truncation chains, a.e. arguments, equality
cases in sharp inequalities) are exactly where a proof assistant adds real
assurance. The formal-mathfin open-problems catalogue currently lists this
problem (MF-OP-008) as a reported resolution *"with the proof not independently
checked"*; this repository is that check, for the pointwise-maximisation
version of the theorem (see the scope notes below).

## The theorem

Paper **Theorem 1.1** (v4), formalized and proved:

- `KyleModel Ω`: any probability space carrying independent `V ~ N(μ₀, τ²)`,
  `U ~ N(0, σ²)`, `τ, σ > 0` (distribution-level, exactly the paper's model).
  `generalModel μ₀ τ σ hτ hσ` proves the class is inhabited at every admissible
  parameter triple; `stdModel = generalModel 0 1 1` is the normalised instance.
- `IsPricingRule`: market efficiency, a Borel `P` with
  `P (Y_φ) = E[V ∣ σ(Y_φ)]` a.s., via Mathlib's `condExp`.
- `IsEquilibrium`: **the paper's pair notion**, `(φ, P)` with `φ` Borel, `P` a
  pricing rule for `φ`, and for **every** `v`, the order `φ v` maximizing
  expected profit `E[(v − P (x + U)) * x]` over **all** `x : ℝ`.
- **`kyle_equilibrium_pair_iff`**: `(φ, P)` is an equilibrium **iff**
  `φ = fun v ↦ (σ/τ) * (v − μ₀)` (eq. (1.1)) **and** `P` prices affinely along
  the flow almost surely, `P (Y_φ) = μ₀ + (τ/(2σ)) · Y_φ` (eq. (1.2)). Strategy
  uniqueness is exact function equality over all Borel strategies; pricing-rule
  uniqueness is up to null modification, matching the paper's phrasing. Also
  packaged strategy-only (`kyle_unique_equilibrium`) and as `∃!`
  (`kyle_existsUnique_equilibrium`).

The whole chain behind it is proved too: **Proposition 4.1** (`|Γ| ≤ 1/2` with
the affine saturation cases, for every Borel strategy), **Proposition 5.1** (the
accounting identity `Γ = E[Π(V)]`), **Proposition 6.1** (`Γ = 1/2` under
pointwise maximisation, including the signed-root construction inside its
proof), **Theorem 7.1** (rigidity: the maximisation condition holds iff
`φ = id`), and **Lemmas 2.1–2.6, 3.1, 3.2**.

Every statement carries a comment citing the paper section or equation it
tracks, and every departure from the paper's text is written down in
[`STATEMENT_NOTES.md`](STATEMENT_NOTES.md) and summarised below.

## Status

**Complete.** From-scratch `lake build`: exit 0, 3149 jobs, 0 errors, 0
warnings, **0 `sorry`**, 0 `sorryAx`. 19 Lean files, about 10,200 lines.

| Paper result (v4) | Lean | Module | Status |
|---|---|---|---|
| **Theorem 1.1**: the equilibrium pair is Kyle's | `kyle_equilibrium_pair_iff`, `kyle_unique_equilibrium`, `kyle_existsUnique_equilibrium`, `isEquilibrium_eq_kyleStrategy` | `Main.lean` | ✅ proved |
| Theorem 1.1, existence half | `kyleStrategy_isEquilibrium`, `kyleStrategy_kylePricingRule_isEquilibrium` | `Statement.lean` | ✅ proved |
| Theorem 1.1, pricing rigidity (1.2) | `pricingRule_ae_eq_kylePricingRule`, `eq_kylePricingRule_of_continuous` | `Statement.lean` | ✅ proved |
| **Theorem 7.1**: rigidity `φ = id` | `isGammaSolution_zero_iff`, `existsUnique_zeroSolution` | `Main.lean` | ✅ proved |
| **Proposition 6.1**: covariance saturation `Γ = 1/2` | `gamma_eq_half`; signed root `criticalPoint`, `signedRoot`, `rootSlope`, `integral_sq_signedRoot`, `integral_inv_sq_rootSlope`, `one_le_two_mul_noiseTraderLoss` | `Main.lean`, `SignedRoot.lean` | ✅ proved |
| **Proposition 5.1**: accounting identity `Γ = E[Π(V)]` | `accounting_identity`, `replica_identity` | `Accounting.lean` | ✅ proved |
| **Proposition 4.1**: `\|Γ\| ≤ 1/2`, affine saturation | `noiseTraderLoss_le_half`, `noiseTraderLoss_eq_half_iff`, `_eq_neg_half_iff`, `integrable_noiseTraderLoss` | `Statement.lean` | ✅ proved |
| **Lemmas 3.1 / 3.2**: `Γ` well defined; `Π` finite and Borel | `noiseTraderLoss_eq_integral_deriv`, `covariance_noise_condExp_eq_noiseTraderLoss`, `insiderProfit_apply`, `measurable_insiderProfit` | `Loss.lean`, `ValueFunction.lean` | ✅ proved |
| **Lemma 2.1**: joint and flow densities, `p > 0` | `map_value_orderFlow`, `lemma21_flowDensity_pos`, `KyleModel.map_orderFlow` | `Posterior.lean`, `Statement.lean` | ✅ proved |
| **Lemma 2.2**: `P` continuous, `P(Y) = E[V∣Y] ∈ L²`, `π_y` | `lemma21_isPricingRule`, `lemma21_continuous`, `lemma22_memLp_two`, `posterior` | `Statement.lean`, `Posterior.lean` | ✅ proved |
| **Lemma 2.3**: `F ∈ C¹`, (2.1)–(2.3), tower clause | `lemma23_integrable`, `hasDerivAt_gaussianSmoothing`, `continuous_deriv_gaussianSmoothing`, `gaussianSmoothing_comp_ae_eq_condExp_condExp` | `Statement.lean`, `Regularity.lean`, `Resampling.lean` | ✅ proved |
| **Lemma 2.4**: value function, FOC, (2.4)–(2.6), (A.1) | `insiderProfit`, `insiderProfit_eq_iSup`, `firstOrderCondition`, `ae_hasDerivAt_insiderProfit`, `strictMono_of_isGammaSolution` | `ValueFunction.lean` | ✅ proved |
| **Lemma 2.5**: `P′ = Cov_{π_y}(id,φ) > 0`, `F′ > 0` | `deriv_inverseRegression_eq_cov`, `deriv_inverseRegression_pos`, `deriv_gaussianSmoothing_pos` | `Posterior.lean` | ✅ proved |
| **Lemma 2.6**: conditional resampling, clauses (i)–(iv) | `resamplingMeasure` + `_map_swap`, `_map_fst`, `_map_snd`, `integral_v1_mul_eq_inverseRegression` | `Resampling.lean` | ✅ proved |
| One-sided Gaussian (Stein-type) inequality for monotone functions | `one_le_sqrt_integral_sq_mul_integral_inv_sq` | `SteinInequality.lean` | ✅ proved, **our route, not v4's** (see F1) |
| **Lemma 2.7** (Cacoullos lower variance bound) | none | none | ❌ not formalized (F1) |
| **Appendix B** (a.e. maximisation, quasi-equilibrium) | none | none | ❌ out of scope (F11) |
| Beyond the paper: cubic-root layer of v2's deleted quadratic-cost family | `betaGamma`, `lambdaGamma`, … | `BeyondPaper.lean` | ✅ proved, fenced as beyond-paper |

## Faithfulness and deviations

Twelve things about the formalization differ from the paper's text. None is a
soundness gap: they are route choices, wording gaps on clauses nothing
consumes, hypotheses the paper carries as standing assumptions, and one
explicit scope exclusion. Plain-language list below; the version with Lean
declaration names is [`STATEMENT_NOTES.md`](STATEMENT_NOTES.md) §5.

1. **(F1) One step follows the paper's previous version, not this one.** For
   `1 ≤ 2Γ` inside Proposition 6.1, v4 uses a Cacoullos lower Gaussian variance
   bound (its Lemma 2.7). We do not formalize that lemma. We prove the step
   with the **one-sided Stein inequality that was v3's Lemma 2.5** and was
   deleted in v4, proved from Mathlib alone in `SteinInequality.lean`. So for
   this one step the formalized proof is v3's, not v4's. This is the largest
   divergence in the artifact.
2. **(F2) `Γ` is defined by the paper's second expression.** The paper defines
   `Γ := E[U(P(Y) − V)]`; we define it as `E[U·P(Y)]` and *prove* the paper's
   definiens and its `Cov(U, E[V∣Y])` form equal to it.
3. **(F3) "Every Borel version" clauses are stated for the canonical version.**
   Lemma 2.3's version clause and Lemmas 3.1/3.2 are proved for the canonical
   continuous inverse regression. The transfer to arbitrary versions is proved
   machinery (`pricingRule_ae_eq_of_flowPDF_pos`, `expectedProfit_congr_ae`)
   used on the headline path, but it is never packaged as a single
   every-version lemma.
4. **(F4) `π_y` is not formalized as a conditional distribution.** Mathlib's
   `condDistrib` is not used; the posterior is an explicit measure and only the
   consequences the proof needs are proved.
5. **(F5) Continuity of `P′` is not stated.** Differentiability everywhere, the
   covariance formula and strict positivity are. Nothing downstream uses
   continuity. (The `C¹` clause for `F` *is* fully proved.)
6. **(F6) Conditional resampling is an explicit measure on `ℝ³`**, built by one
   `withDensity`, rather than Kallenberg's transfer theorem on an extended
   space; conditional i.i.d.-ness is not stated, and clauses (iii)/(iv) are in
   bounded-test-function form (equivalent, given the proved integrability).
7. **(F7) The value function is defined at its attained value**,
   `Π(v) = φ(v)(v − F(φ(v)))`, not as a supremum allowing `+∞`; the
   identification with the supremum is proved (`insiderProfit_eq_iSup`). So
   nonnegativity and convexity carry the maximisation hypothesis, where the
   paper has them for arbitrary `φ`.
8. **(F8) `kyle_equilibrium_pair_iff` carries an explicit `Measurable P`**,
   which the paper folds into its standing "Borel-measurable pricing rule"
   sentence.
9. **(F9) The accounting identity carries a redundant `Measurable φ`**
   alongside `Monotone φ`.
10. **(F10) Two theorems are stronger than the paper's.** `gamma_eq_half` and
    `isGammaSolution_zero_iff` assume only pointwise maximisation, not
    equilibrium, which is what the paper's own proofs reduce to.
11. **(F11) Appendix B is not formalized.** The a.e.-maximisation variant (in
    which the equilibrium strategy is unique only modulo null sets) is out of
    scope. **Theorem 1.1 here is scoped to the pointwise-maximisation
    definition.**
12. **(F12) §7 standardises the laws, not the probability space.** The
    equilibrium-transfer biconditional of §7 is never stated; only the
    direction the headline needs is proved.

The universally quantified headline theorems are not vacuous: `generalModel`
inhabits `KyleModel` at every admissible `(μ₀, τ, σ)`, and the oracles
`generalModel_priceImpact` (`λ = τ/(2σ)`) and `generalModel_kyleStrategy`
(`φ(v) = (σ/τ)(v − μ₀)`), with numeric instances at `(3, 2, 5)`, exhibit Kyle's
price impact and strategy away from the normalised point.

## Module map

```
KyleUniqueness/
  Definitions.lean       -- model, order flow, pricing rule, equilibrium pair, Γ,
                            stdModel, generalModel (inhabitants at all parameters)
  GaussianHelpers.lean   -- ϱ toolkit, tail FTC, null-singleton glue   (Mathlib-only)
  SteinInequality.lean   -- one-sided Gaussian inequality              (Mathlib-only)
  CondExpBridge.lean     -- explicit Bayes quotient ↔ condExp
  Statement.lean         -- Lemmas 2.1-2.3 layer, Prop 4.1, affine regression
  Regularity.lean        -- F ∈ C¹, eq. (2.3)
  PosteriorDeriv.lean    -- differentiation under the integral for n, p, P
  ValueFunction.lean     -- Lemma 2.4: Π, FOC, (2.4)-(2.6), (A.1)
  Posterior.lean         -- Lemma 2.1 joint density, §2.2 π_y, Lemma 2.5
  Resampling.lean        -- Lemma 2.6 (i)-(iv), Lemma 2.3 tower clause
  Loss.lean              -- Lemmas 3.1/3.2
  Accounting.lean        -- Proposition 5.1
  SignedRoot.lean        -- the signed-root construction inside Prop 6.1; 1 ≤ 2Γ
  Main.lean              -- Prop 6.1, Theorem 7.1, §7 standardisation, THEOREM 1.1
  AxiomAudit.lean        -- #print axioms harness, runs at every build
  BeyondPaper.lean       -- v2-legacy cubic layer, fenced
```

Pieces that Mathlib lacks and that could be upstreamed: the one-sided Gaussian
inequality for monotone functions and the Stieltjes-dominates-a.e.-derivative
lemma behind it (`SteinInequality.lean`, **zero project imports**), the
Bayes-quotient/`condExp` bridge (`CondExpBridge.lean`), and the Gaussian helper
toolkit (`GaussianHelpers.lean`).

## How to verify

```bash
# toolchain: elan installs the pin automatically from lean-toolchain
git clone https://github.com/shehral/kyle-uniqueness-lean && cd kyle-uniqueness-lean
lake exe cache get     # fetch the Mathlib olean cache
lake build             # the verification: green, zero sorries
```

`lake build` (Lean `v4.32.0`, Mathlib `81a5d257` = tag `v4.32.0`) must finish
with **zero errors, zero warnings, and zero `declaration uses 'sorry'`**. The
axiom audit runs as part of it:

```bash
lake build 2>&1 | grep -c "declaration uses"                     # 0
lake build 2>&1 | grep -o "depends on axioms: \[.*\]" | sort -u   # one line:
#   depends on axioms: [propext, Classical.choice, Quot.sound]
```

(On a second, fully cached build these greps print nothing; delete
`.lake/build` and rebuild to see the audit lines again.)
`KyleUniqueness/AxiomAudit.lean` carries 405 `#print axioms` lines, one for every
public named declaration in the tree; the only omissions are four anonymous
`instance`s with machine-generated names. There are no `axiom` declarations, no
`native_decide`, no `unsafe`/`partial`/`opaque`/`@[extern]`/`@[implemented_by]`,
and no `set_option` suppressions. CI runs the same build on every push.
Environment notes: [`SETUP.md`](SETUP.md).

## Timeline

The git history is the original working history (dates as committed). Work
before the first commit was banked into it.

| Date | Event |
|---|---|
| 2026-07-26 | arXiv:2607.23585 v1 posted (v2 on 08-01, v3 on 08-10) |
| 2026-08-11/12 | Statement layer written against v2, reconciled to v3; canary statements proved (definitions are not vacuous); Session 1 closes 12 of 14 `sorry`s |
| 2026-08-18 | Session 2: the Stein pipeline (`SteinInequality.lean`), `F ∈ C¹`, differentiation under the integral. First commits in this repository |
| 2026-08-20 | arXiv v4 posted (rewritten §4 proof apparatus) |
| 2026-09-16 | v4 reconciliation, then Session 3 in three waves: the remaining two headline carriers closed, **0 `sorry`**; closeout audit and the general-parameter inhabitant |
| 2026-11-03 | Public release v1.0.0, archived on Zenodo |

The session-by-session record, including routes taken and dead ends, is
[`PROVING_LOG.md`](PROVING_LOG.md); the proof plan node by node is
[`blueprint/blueprint.md`](blueprint/blueprint.md) (v3-keyed, historical).

## AI-assistance disclosure

This project was built with substantial AI assistance, and says so plainly:
**the Lean statements, proofs, and documentation were drafted by Claude Code
(Anthropic's agentic coding tool), including multi-agent proving waves in which
a prover agent's work on each module was checked by an independent adversarial
verifier agent, under the direction of Mohammad Ali Shehral, who set the
target, the fidelity frame, and the review bar.** Route decisions taken by the
agent under explicit delegation are recorded as D1–D9 in
[`blueprint/LANE_C_DECISIONS_2026-09-16.md`](blueprint/LANE_C_DECISIONS_2026-09-16.md);
three of them are the source of deviations F1, F6 and F7. The mathematics being
verified is Monteiro and Tourky's. A machine-readable disclosure in the
formal-mathfin `formalization.yaml` format is at
[`formalization.yaml`](formalization.yaml). Nothing here rests on trusting the
process: the claim surface is exactly what `lake build` accepts, and Lean's
kernel checks every proof.

## Contributing

The headline is closed, so the open work is breadth and upstreaming:

1. **Upstream the Mathlib-shaped pieces**: the one-sided Gaussian inequality
   and its Stieltjes domination lemma, the Bayes-quotient/`condExp` bridge, the
   Gaussian helper toolkit.
2. **Close the deviations worth closing**: Cacoullos's lower Gaussian variance
   bound (which would make Proposition 6.1's proof v4's own, F1), continuity
   of `P′` (F5), a single every-version statement of Lemmas 3.1/3.2 (F3), `π_y`
   as a `condDistrib` (F4).
3. **Formalize Appendix B** (F11), the a.e.-maximisation variant.
4. PRs must keep `lake build` green, introduce no `sorry`, add no axioms, and
   extend `AxiomAudit.lean` for any new headline declaration. Please state AI
   assistance in your PR if you used it.

## Citation and license

Apache 2.0 (see [LICENSE](LICENSE)). The mathematics is Monteiro and Tourky's;
this repository is a formalization of it. If you use this artifact, cite the
Zenodo deposit ([doi:10.5281/zenodo.23912107](https://doi.org/10.5281/zenodo.23912107); see
[`CITATION.cff`](CITATION.cff)) and the source paper:

> P. K. Monteiro, R. Tourky. *The one-period Kyle model has one equilibrium.*
> arXiv:2607.23585v4, 2026.

(The paper was retitled twice: v2 *"Monotonicity and Rigidity in Gaussian
Inverse Regression: The One-Period Kyle Model Has a Unique Equilibrium"*, v3
*"The one-period Gaussian Kyle model has exactly one equilibrium"*. This
formalization tracks **v4**.)

Related: [Mathlib](https://github.com/leanprover-community/mathlib4) ·
[formal-mathfin](https://github.com/formal-applied-math/formal-mathfin), whose
disclosure and axiom-audit patterns this repository adopts.
