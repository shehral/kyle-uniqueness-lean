/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# The one-period Kyle model: definitions

Formalization of the model of Monteiro & Tourky, *The one-period Kyle model
has one equilibrium* (arXiv:2607.23585, **v4** of 2026-08-20). This file
contains only definitions and a handful of elementary lemmas; the paper's
theorems are stated in `KyleUniqueness.Statement` and `KyleUniqueness.Main`.

## Contents

* **The general model (paper §1).** `KyleModel` packages the primitives: a
  probability space, the asset value `V ~ N(μ₀, τ²)` and independent noise
  demand `U ~ N(0, σ²)`, with `τ, σ > 0`. On top of it:
  `KyleModel.orderFlow` (`Y_φ = φ(V) + U`), `KyleModel.IsPricingRule`
  (competitive pricing `P_φ(Y_φ) = E[V ∣ Y_φ]` a.s. — item 2 of §1's
  equilibrium definition), `KyleModel.expectedProfit` (the expectation in
  the profit-maximisation condition), `KyleModel.IsEquilibrium` (**v4's
  primary notion**: a (strategy, pricing-rule) *pair* is an equilibrium),
  `KyleModel.IsEquilibriumStrategy` (the derived `∃ P`-projection),
  `KyleModel.kyleStrategy` (eq. (1.1)) and `KyleModel.kylePricingRule`
  (eq. (1.2)).

* **The normalised model (paper §2).** `V`, `U` standard normal. The objects
  `flowDensity` (`p(y)`, Lemma 2.1), `inverseRegression` (`P`, the explicit
  Bayes quotient by which v4 §2.2 *defines* the pricing rule — see the note
  on the definition), `gaussianSmoothing` (`F`, eqs. (2.1)–(2.2)),
  `noiseTraderLoss` (`Γ`, v4 §3.1 — the organising quantity of the proof;
  v4 changed its definiens, see the note on `noiseTraderLoss`), `objective`
  and `IsGammaSolution` (whose `γ = 0` instance is the paper's
  pointwise-maximisation condition, untagged in v4, with the value function
  `Π` of v4 §2.4 / Lemma 3.2). `stdModel` realises the normalised model as a
  `KyleModel` on the canonical space `ℝ × ℝ`.

The cubic-root layer (`betaGamma`, `lambdaGamma`) that supported v2's
deleted quadratic-cost family now lives in `KyleUniqueness.BeyondPaper`.

All section, equation and lemma numbers in this file refer to
arXiv:2607.23585 **v4**. Earlier sessions of this development were keyed to
v3 (and, before that, v2): the v2 ↔ v3 map is recorded in
`STATEMENT_NOTES.md` and `V3_RECONCILIATION_PLAN.md`, and the v3 → v4
crosswalk in `V4_DELTA_REPORT_2026-09-16.md` §1 (repo policy:
`blueprint/LANE_C_DECISIONS_2026-09-16.md`, decision D1). None of v3's flat
equation numbers survives into v4's per-section numbering, so a bare v3
number appearing below would be a bug, not a variant spelling.
-/

open MeasureTheory ProbabilityTheory

namespace KyleUniqueness

/-! ## The general model (paper §1)

"a risk-neutral informed trader observes the asset value `V ~ N(μ,τ²)`. …
Liquidity traders submit an aggregate order `U ~ N(0,σ²)`, independent of `V`,
with `τ,σ > 0`." (§1, first paragraph). We write `μ₀` for the prior mean that
the paper calls `μ`, freeing `μ` for the ambient probability measure.
Variances are passed to `gaussianReal` as the nonnegative reals
`⟨τ ^ 2, _⟩`, `⟨σ ^ 2, _⟩`. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The primitives of the one-period Kyle model (paper §1, first paragraph):
a probability space carrying the asset value `V ~ N(μ₀, τ²)` and the noise
demand `U ~ N(0, σ²)`, independent, with `τ, σ > 0`. Strategies and pricing
rules are NOT part of the model data; they are quantified in the definitions
below, exactly as in the paper. -/
structure KyleModel (Ω : Type*) [MeasurableSpace Ω] where
  /-- The ambient probability measure. -/
  μ : Measure Ω
  /-- `μ` is a probability measure. -/
  hprob : IsProbabilityMeasure μ
  /-- The prior mean of the asset value (the paper's `μ`). -/
  μ₀ : ℝ
  /-- The standard deviation of the asset value. -/
  τ : ℝ
  /-- The standard deviation of the noise-trader demand. -/
  σ : ℝ
  /-- Nondegeneracy: `τ > 0` (§1). -/
  hτ : 0 < τ
  /-- Nondegeneracy: `σ > 0` (§1). -/
  hσ : 0 < σ
  /-- The asset value observed by the informed trader. -/
  V : Ω → ℝ
  /-- The aggregate noise-trader (liquidity) demand. -/
  U : Ω → ℝ
  /-- `V` is a random variable. -/
  hV : Measurable V
  /-- `U` is a random variable. -/
  hU : Measurable U
  /-- `V ~ N(μ₀, τ²)` (§1). -/
  hVlaw : μ.map V = gaussianReal μ₀ ⟨τ ^ 2, sq_nonneg τ⟩
  /-- `U ~ N(0, σ²)` (§1). -/
  hUlaw : μ.map U = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩
  /-- `U` is independent of `V` (§1). -/
  hIndep : IndepFun V U μ

/-- The probability-measure field, made available to instance search. -/
instance (M : KyleModel Ω) : IsProbabilityMeasure M.μ := M.hprob

namespace KyleModel

variable (M : KyleModel Ω)

/-- The aggregate order flow `Y_φ = φ(V) + U` observed by the market makers
(paper §1, display before eq. (1)). -/
def orderFlow (φ : ℝ → ℝ) : Ω → ℝ := fun ω => φ (M.V ω) + M.U ω

/-- The σ-algebra `σ(Y_φ)` generated by the order flow: the market makers'
information. -/
@[reducible]
def flowSigma (φ : ℝ → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (M.orderFlow φ) inferInstance

/-- A pricing rule for the strategy `φ` (item 2 of the paper's §1
equilibrium definition — "competitive pricing"): a Borel `P_φ : ℝ → ℝ` with
`P_φ(Y_φ) = E[V ∣ Y_φ]` almost surely. The conditional expectation is
Mathlib's `condExp` with respect to `σ(Y_φ)`. This determines `P_φ` only up
to null sets of the law of `Y_φ` (v4 states all pricing-rule uniqueness
a.s. / up to Lebesgue-null modification accordingly). v4 renames this
condition "market efficiency" (v3: "competitive pricing"). -/
structure IsPricingRule (φ : ℝ → ℝ) (P : ℝ → ℝ) : Prop where
  /-- The pricing rule is Borel measurable. -/
  measurable : Measurable P
  /-- Zero-profit / competitive pricing: `P_φ(Y_φ) = E[V ∣ Y_φ]` a.s. -/
  ae_eq_condExp :
    (fun ω => P (M.orderFlow φ ω)) =ᵐ[M.μ] MeasureTheory.condExp (M.flowSigma φ) M.μ M.V

/-- The insider's expected profit `E[(v − P(x + U)) x]` from submitting the
market order `x` after observing `V = v`, with the pricing rule `P` held
fixed — the two sides of the paper's §1 profit-maximisation condition.
(Finiteness of this integral for any Borel version of the pricing rule, and
its independence of the chosen version, are *stated paper lemmas* — v4
Lemmas 2.2 and 2.3 — so the Bochner integral is the honest expectation on
the entire class the theorems quantify over.) -/
noncomputable def expectedProfit (P : ℝ → ℝ) (v x : ℝ) : ℝ :=
  ∫ ω, (v - P (x + M.U ω)) * x ∂M.μ

/-- **v4's primary equilibrium notion (§1, Theorem 1.1): the pair.**
A pair `(φ, P)` is an equilibrium iff (i) `φ` is Borel, (ii) `P` is a
pricing rule for `φ` (competitive pricing, item 2 of the definition), and
(iii) the order `φ(v)` maximises the insider's expected profit against `P`
at EVERY `v ∈ ℝ`:
`E[(v − P(φ(v)+U)) φ(v)] ≥ E[(v − P(x+U)) x]` for every `v, x ∈ ℝ`
(item 1). v4 names the two items "Profit maximisation" and "Market
efficiency" (v3: "pointwise profit maximisation" / "competitive pricing").
Note the quantifier: every `v`, not almost every `v`. v4 remarks in
footnote 1 that a.e.-maximisation suffices and defers the quasi-equilibrium
statement to Appendix B, Lemma B.1; v3 cited its own Lemma 2.7 at this
point, which v4 DELETED (v4's Lemma 2.7 is the unrelated Cacoullos variance
bound). The primary definition is pointwise, and so is ours — Appendix B is
not formalized; see `KyleUniqueness.Main`. -/
structure IsEquilibrium (φ P : ℝ → ℝ) : Prop where
  /-- The strategy is Borel measurable (§1: "Borel function `φ`"). -/
  measurable : Measurable φ
  /-- Competitive pricing: `P` is a pricing rule for `φ`. -/
  pricingRule : M.IsPricingRule φ P
  /-- Pointwise profit maximisation at every `v`. -/
  isMaxOn : ∀ v x : ℝ, M.expectedProfit P v x ≤ M.expectedProfit P v (φ v)

/-- Kyle's profit-maximisation equilibrium, strategy-only form: `φ` is an
equilibrium strategy if it is Borel and profit-maximising against SOME
pricing rule — the `∃ P`-projection of `IsEquilibrium`. (v2 took this as
the primary notion; v3 and v4 promote the pair. The two are interchangeable:
whether the maximisation condition holds does not depend on the chosen
version of the pricing rule — v4 Lemmas 2.2/2.3 — and quantifying
existentially makes the equilibrium predicate weakest, hence the uniqueness
theorem strongest. See `isEquilibriumStrategy_iff_exists`.) -/
def IsEquilibriumStrategy (φ : ℝ → ℝ) : Prop :=
  Measurable φ ∧
    ∃ P : ℝ → ℝ, M.IsPricingRule φ P ∧
      ∀ v x : ℝ, M.expectedProfit P v x ≤ M.expectedProfit P v (φ v)

variable {M} in
/-- An equilibrium pair projects to an equilibrium strategy. -/
theorem IsEquilibrium.isEquilibriumStrategy {φ P : ℝ → ℝ}
    (h : M.IsEquilibrium φ P) : M.IsEquilibriumStrategy φ :=
  ⟨h.measurable, P, h.pricingRule, h.isMaxOn⟩

/-- The strategy-only notion is exactly the `∃ P`-projection of v4's pair
notion. -/
theorem isEquilibriumStrategy_iff_exists (φ : ℝ → ℝ) :
    M.IsEquilibriumStrategy φ ↔ ∃ P : ℝ → ℝ, M.IsEquilibrium φ P :=
  ⟨fun ⟨hφ, P, hPR, hmax⟩ => ⟨P, hφ, hPR, hmax⟩,
    fun ⟨_, h⟩ => h.isEquilibriumStrategy⟩

/-- Kyle's affine strategy `φ(v) = (σ/τ)(v − μ₀)` (v4 eq. (1.1)). -/
noncomputable def kyleStrategy : ℝ → ℝ := fun v => M.σ / M.τ * (v - M.μ₀)

/-- Kyle's price-impact coefficient `λ = τ/(2σ)` (v4 eq. (1.2); the
`Cov(V, Y_φ)/Var(Y_φ)` reading, displayed inline in v3, survives in v4 only
as Appendix B's eq. (B.2)). -/
noncomputable def priceImpact : ℝ := M.τ / (2 * M.σ)

/-- Kyle's affine pricing rule `P_φ(y) = μ₀ + λ y`, `λ = τ/(2σ)` (v4
eq. (1.2), stated there a.s. along the flow: `P(Y_φ) = μ + λ Y_φ`). -/
noncomputable def kylePricingRule : ℝ → ℝ := fun y => M.μ₀ + M.priceImpact * y

end KyleModel

/-! ## The normalised model (paper §2)

"Let `V` and `U` be independent standard normal random variables, and let `ϱ`
denote the standard normal density. Throughout, fix a Borel function
`φ : ℝ → ℝ` and set `Y = φ(V) + U`." (§2, opening.)

v4 §2.2 *defines* the pricing rule `P` by the explicit Bayes quotient
(posterior mean) below — the modeling choice that v2 forced on us as a
MATHLIB-GAP workaround is paper-canonical from v3 on. Mathlib (at pin
`81a5d257`, tag v4.32.0) still has no posterior-density / Bayes-quotient API
for `ProbabilityTheory.condDistrib`, so the definition remains explicit and
the bridge back to `condExp` — that this explicit function IS a pricing rule
in the sense of `KyleModel.IsPricingRule` (v4 Lemma 2.2) — is PROVED in
`KyleUniqueness.Statement` (`lemma21_isPricingRule`, the canary). -/

/-- The standard normal density `ϱ` (§2). Equal to
`(√(2π))⁻¹ exp(−x²/2)` by `ProbabilityTheory.gaussianPDFReal_def`. -/
noncomputable def stdNormalPDF : ℝ → ℝ := gaussianPDFReal 0 1

/-- The density `p(y) = E[ϱ(y − φ(V))]` of the law of the order flow
`Y = φ(V) + U` (Lemma 2.1; written as the integral of `ϱ(y − φ(v))` against
the standard Gaussian law of `V`). Lemma 2.1 asserts it is everywhere
positive — stated as `lemma21_flowDensity_pos` in `Statement.lean`. -/
noncomputable def flowDensity (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ v, stdNormalPDF (y - φ v) ∂gaussianReal 0 1

/-- The inverse regression `P`, via the explicit Bayes posterior-mean formula
by which v4 §2.2 defines the pricing rule: `P(y) = ∫ v π_y(dv)` (the last
display of v4 §2.2; the tag v3 gave it, eq. (6), is gone) with posterior
`π_y(dv) = ϱ(v)ϱ(y − φ(v)) dv / p(y)`. v4 Lemma 2.2 asserts
`P` is continuous and `P(Y) = E[V ∣ Y] ∈ L²` a.s. — stated in
`Statement.lean` (`lemma21_isPricingRule` proved, `lemma21_continuous`,
`lemma22_memLp_two`). (Lean's convention `r/0 = 0` is harmless: the
denominator is everywhere positive by Lemma 2.1 —
`lemma21_flowDensity_pos`, proved.) -/
noncomputable def inverseRegression (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ v, v * stdNormalPDF (y - φ v) ∂gaussianReal 0 1) / flowDensity φ y

/-- The Gaussian smoothing `F(x) = E[P(x + U)]` of the inverse regression
(v4 eq. (2.1); v4 eq. (2.2) is the convolution form `∫ P(y)ϱ(y − x) dy`):
the insider's expected price at order size `x`. v4 Lemma 2.3 asserts
`F ∈ C¹` with `F′(x) = ∫ u P(x + u) ϱ(u) du`; v4 tags only the first line of
that split display as (2.3), so this `u`-integral form carries no v4
equation number of its own. No analyticity claim remains anywhere in v3 or
v4. NOTE: v4's Lemma 2.3 is strictly STRONGER than v3's — it additionally
asserts finiteness of the expectation in (2.1) and absolute convergence of
the integrals in (2.2)/(2.3); see `KyleUniqueness.Regularity`. -/
noncomputable def gaussianSmoothing (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u, inverseRegression φ (x + u) ∂gaussianReal 0 1

/-- The noise traders' expected loss `Γ` (v4 §3.1) — the organising quantity
of the proof — realised on the canonical normalised space `ℝ × ℝ`
(coordinates `(V, U)` under the product of two standard Gaussians) through
the explicit inverse regression: `Γ = E[U · P(Y)]`, `Y = φ(V) + U`.

**Definiens note (v3 → v4).** v3's eq. (13) *defined* `Γ := Cov(U, E[V ∣ Y])`;
v4 §3.1 instead *defines* `Γ := E[U(P(Y) − V)]` and demotes the covariance
form to a conclusion of its new Lemma 3.1. This Lean definition is the
middle expression `E[U · P(Y)]`, and BOTH paper readings are proved equal to
it in `KyleUniqueness.Loss`: `integral_noise_mul_sub_value_eq_noiseTraderLoss`
(v4's definiens) and `covariance_noise_condExp_eq_noiseTraderLoss` (the
covariance form). The equalities hold because `E[U] = 0` and
`P(Y) = E[V ∣ Y] ∈ L²` (v4 Lemma 2.2 = `lemma21_isPricingRule` +
`lemma22_memLp_two`).

Finiteness of `Γ` belongs to v4 **Lemma 3.1**: v4's Proposition 4.1 dropped
the "is finite and" that v3's Proposition 2 carried, so
`integrable_noiseTraderLoss` in `Statement.lean` now discharges a clause of
Lemma 3.1, not of Proposition 4.1. Proposition 4.1's own claims —
`−1/2 ≤ Γ ≤ 1/2` (v4 eq. (4.1)) and equality iff `φ(v) = ±v + a`
Lebesgue-a.e. (untagged in v4; v3 eq. (15)) — are also stated in
`Statement.lean`. -/
noncomputable def noiseTraderLoss (φ : ℝ → ℝ) : ℝ :=
  ∫ p, p.2 * inverseRegression φ (φ p.1 + p.2)
    ∂((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- The insider's objective in the normalised model with quadratic trading
cost: `x(v − F(x)) − (γ/2)x²`. The case `γ = 0` is the paper's objective
`x(v − F(x))` — the integrand of the value function `Π` of v4 §2.4 /
Lemma 3.2, untagged in v4 (v3 eq. (8)). The `γ ≠ 0` readings are
**beyond-paper**: the quadratic-cost family of v2's Definition 2.2 was
dropped in v3 and has not returned in v4 (see
`KyleUniqueness.BeyondPaper`). -/
noncomputable def objective (γ : ℝ) (φ : ℝ → ℝ) (v x : ℝ) : ℝ :=
  x * (v - gaussianSmoothing φ x) - γ / 2 * x ^ 2

/-- Pointwise-maximisation solutions: a Borel `φ` with
`φ(v) ∈ argmax_x {x(v − F(x)) − (γ/2)x²}` for every `v ∈ ℝ`, where `F` is
the Gaussian smoothing built from `φ` itself. The instance `γ = 0` is
exactly the paper's pointwise-maximisation condition —
`φ(v) ∈ argmax_x x(v − F(x))` for every `v`, which v3 tagged (17) and v4
leaves untagged — the hypothesis of v4 Proposition 6.1 and Theorem 7.1
(v3: Theorems 3 and 4). The general-`γ` family is v2 legacy, kept as a
definition only (**beyond-paper** for `γ ≠ 0`; no v3 or v4 theorem is stated
about it — see `KyleUniqueness.BeyondPaper`). -/
def IsGammaSolution (γ : ℝ) (φ : ℝ → ℝ) : Prop :=
  Measurable φ ∧ ∀ v x : ℝ, objective γ φ v x ≤ objective γ φ v (φ v)

/-- `⟨1², _⟩ = 1` in `ℝ≥0` — glue for the `stdModel` law fields. -/
private lemma nnreal_one_sq : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : NNReal) = 1 := by
  norm_num

/-- The normalised model (§2) realised as a `KyleModel` on the canonical
space `ℝ × ℝ`: `V` and `U` are the coordinates under the product of two
standard Gaussians, `μ₀ = 0`, `τ = σ = 1`. This ties the normalised objects
of §2 to the general equilibrium definition of §1 (see
`equilibrium_iff_zeroSolution` in `Statement.lean`, the `σ = τ = 1` case of
the location–scale standardisation in the proof of Theorem 1.1 — v4 §7,
v3 §3.1). -/
noncomputable def stdModel : KyleModel (ℝ × ℝ) where
  μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  hprob := inferInstance
  μ₀ := 0
  τ := 1
  σ := 1
  hτ := one_pos
  hσ := one_pos
  V := Prod.fst
  U := Prod.snd
  hV := measurable_fst
  hU := measurable_snd
  hVlaw := by rw [nnreal_one_sq]; exact MeasureTheory.measurePreserving_fst.map_eq
  hUlaw := by rw [nnreal_one_sq]; exact MeasureTheory.measurePreserving_snd.map_eq
  hIndep := by
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable,
      MeasureTheory.measurePreserving_fst.map_eq,
      MeasureTheory.measurePreserving_snd.map_eq]
    exact Measure.map_id

end KyleUniqueness
