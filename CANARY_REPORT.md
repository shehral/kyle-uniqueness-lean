# CANARY_REPORT — definitional-fidelity gate, Kyle-uniqueness formalization

Date: 2026-08-12. Toolchain: Lean `v4.32.0`, Mathlib `81a5d257` (tag
v4.32.0). Paper: Monteiro & Tourky, arXiv:2607.23585v2.
**Local only — nothing published, pushed, or announced.**

## Verdict up front

**Both canaries PROVED, sorry-free, axiom-clean, with ZERO changes to any
definition.** The paper's linear equilibrium is an equilibrium under our
`IsEquilibriumStrategy`/`IsPricingRule`/`expectedProfit` exactly as they
were frozen in the statement phase, and the explicit Bayes-quotient
`inverseRegression` is a genuine pricing rule under the same untouched
definitions. No definitional defect surfaced anywhere. The
definitional-fidelity gate is **GO**.

| Canary | Statement | Status | Axioms |
|---|---|---|---|
| 1 | `kyleStrategy_isEquilibrium` (Thm 1.1, existence half; sorry #11) | **proved** | `[propext, Classical.choice, Quot.sound]` |
| 2 | `lemma21_isPricingRule` (Lemma 2.1 / eq. (10) bridge; sorry #2) | **proved** | `[propext, Classical.choice, Quot.sound]` |

Also closed en route (same infrastructure, listed in the audit):

| Bonus | Statement | Status |
|---|---|---|
| sorry #1 | `lemma21_flowDensity_pos` (Lemma 2.1, `p > 0`) | **proved** |
| sorry #13 | `isPricingRule_kylePricingRule` (eq. (3)) | **proved** |

`lake build`: **green, 3116 jobs, 0 errors, 0 non-`sorry` warnings.**
Sorry count: **14 → 10** (all remaining in `Statement.lean`).
Axiom audit (`AxiomAudit.lean`, runs at every build): every proved
declaration — including all new infrastructure — depends only on
`[propext, Classical.choice, Quot.sound]`; every still-sorried statement
additionally on `sorryAx`, as expected.

## What the canaries certify (and what they do not)

The statement phase flagged (STATEMENT_NOTES §5) the residual risk that a
subtly wrong definition — e.g. a wrong σ-algebra making `IsPricingRule`
empty — would leave the uniqueness theorem vacuously provable. The two
canaries were chosen as exactly the statements that would then be
UNPROVABLE. They are now proved, which certifies:

* `KyleModel.IsPricingRule`'s `condExp (flowSigma φ) M.μ M.V` condition is
  satisfiable, with the paper's own eq. (3) rule as witness — the
  `comap`-σ-algebra, the junk-value conventions of `condExp` (C3), and the
  a.s.-equality all line up so that the intended object qualifies.
* `KyleModel.expectedProfit`'s Bochner integral (C5) evaluates to the
  paper's finite expectation against the affine rule — the quadratic
  `(v − μ₀ − λx)x` comes out exactly, and its maximiser is `kyleStrategy v`
  for EVERY `v` (the C6 quantifier), so eq. (1) holds non-vacuously.
* The `∃ P`-version quantification (C4) admits the natural witness.
* The explicit `inverseRegression` (C7/GAP-1) is a version of
  `E[V ∣ Y]` for EVERY Borel strategy on `stdModel` — the Bayes-quotient
  reading of the MATHLIB-GAP workaround is correct, for the whole strategy
  class, not just nice φ.

Not yet certified (unchanged risk, now small): the *uniqueness* halves
(sorries #8, #12) and the version-independence/continuity layer (#3–#5,
#14), plus the Fubini bridge `equilibrium_iff_zeroSolution` (#6). None of
these can silently weaken the headline: they are theorems to prove, not
definitions to trust.

## Proof-effort notes

### Canary 1 — `kyleStrategy_isEquilibrium` (graded medium; came in as budgeted)

Decomposition (all in `KyleUniqueness/CondExpBridge.lean`):

1. **Pricing-rule bridge** (`isPricingRule_of_forall_mul_flowPDF`) — the
  general-model lemma: any Borel `Q` with `Q·p_φ = n_φ` pointwise is a
  pricing rule, where `p_φ/n_φ` are the (value-weighted) order-flow
  densities. Route: `ae_eq_condExp_of_forall_setIntegral_eq`, indicator
  test functions, transfer to the product space via
  `IndepFun ⇒ map_prod = prod_map` (§1's independence), inner-noise
  translation `∫ f(φv+u) ρ(du) = ∫ ϱ_σ(y−φv) f(y) dy`, one Fubini swap,
  and the pointwise density identity. This is blueprint node **P1 (direct
  route) done early**, and it is strategy-generic — N1/O1 will reuse it
  verbatim. The single load-bearing integrability fact is the Tonelli
  bound `∫∫ |Q(y)|·ϱ_σ(y−φv) dν dy = ∫|n_φ| ≤ E|V| < ∞`, derived FROM the
  density identity itself, so the bridge needs no growth hypothesis on `Q`.
2. **Complete-the-square** (`gaussianPDFReal_mul_gaussianPDFReal_kyle`,
  in `GaussianHelpers.lean`): `ϱ_{σ²}(y−(σ/τ)a)·ϱ_{τ²}(a)
  = ϱ_{2σ²}(y)·ϱ_{τy/(2σ), τ²/2}(a)` — one `field_simp; ring` after
  separating prefactor and exponent. Gives `p(y) = ϱ_{2σ²}(y)` and
  `n(y) = ϱ_{2σ²}(y)(μ₀ + λy)`, i.e. eq. (3)'s identity `P·p = n`.
3. **Profit quadratic** (`expectedProfit_kylePricingRule(_le)`):
  `E[(v−(μ₀+λ(x+U)))x] = (v−μ₀−λx)x` by `E U = 0`; optimality is
  `sub_nonneg` of `λ(x − φ(v))²`.

Effort: ~700 LOC of new infrastructure (bridge 500, helpers 200), one
session. Zero definitional friction — the statement-phase definitions
composed exactly as designed.

### Canary 2 — `lemma21_isPricingRule` (graded medium; came in cheap off the bridge)

With the bridge in place, canary 2 reduced to: (i) `p > 0` everywhere
(`lemma21_flowDensity_pos`: strictly positive bounded integrand,
probability measure, `integral_pos_iff_support_of_nonneg_ae`), (ii)
measurability of the Bayes quotient
(`StronglyMeasurable.integral_prod_right'` on numerator and denominator),
(iii) `(n/p)·p = n` by `div_mul_cancel₀`. ~60 LOC. The stdModel
specialisations (`stdModel_flowPDF/Num`) are `rfl`-grade.

### Tier-0 items also delivered

* **0.1 `GaussianHelpers.lean`** — audit-§10 MISSING items 1–4, all
  proved: `hasDerivAt_gaussianPDFReal` (+ std corollary), the Gaussian
  tail FTC `∫_{Ioi a} x·ϱ = ϱ(a)`, atomlessness transfer glue
  (`withDensity`, injective pushforward, null diagonal,
  positive-measure ⇒ infinite), plus the translation/moment toolkit and
  the complete-the-square identity.
* **0.4 `IdentityTheoremSpike.lean`** — the falsify-early probe for hard
  block 5 SUCCEEDED: `analyticOnNhd_eq_zero_of_measure_ne_zero` (analytic
  `G`, zero set of positive atomless measure ⇒ `G ≡ 0`) is proved in ~10
  lines. The feared `AccPt → ∃ᶠ` glue is one rewrite
  (`accPt_iff_frequently_nhdsNE`).

## Audit corrections discovered (update to `blueprint/mathlib_api_audit.md`)

1. **§10 item 1 was NOT missing.** The atoms API was renamed at this pin:
  `NoAtoms` → `MeasureTheory.NullSingletonClass` (deprecated alias dated
  2026-06-09), and `nullSingletonClass_gaussianReal` (for `v ≠ 0`)
  already exists — the audit's case-sensitive grep for `NoAtoms` missed
  it. Also present under the new name: `Set.Countable.measure_zero`,
  `Set.Finite.measure_zero`.
2. **Bonus find:** `exists_accPt_of_nullSingletonClass` (positive measure
  ⇒ accumulation point) already exists at the pin — it replaces the
  entire "positive measure ⇒ infinite ⇒ Bolzano–Weierstrass" chain
  budgeted for L2 (audit §9 last row). Hard block 5's remaining content
  is only the `F/x` ODE patch and pushforward atomlessness (the latter
  now proved in `GaussianHelpers`).
3. `integrable_id_gaussianReal` is not at the pin under that name
  (derived in one line from `memLp_id_gaussianReal`); now provided.

## Toolchain gotchas hit (for future sessions; extends SETUP.md)

* **NNReal anonymous constructors are simp-opaque**: `⟨σ², _⟩`-variance
  arguments defeat `simp [NNReal.coe_mk]` inside `gaussianPDFReal` goals
  ("not type-correct under instances transparency"). Fix: the rfl-lemma
  `gaussianPDFReal_eval` rewrites the whole pdf application into clean
  real algebra first.
* **`HasDerivAt.mul/.pow` instance diamond**: the NormedRing-path
  instances (`normedCommRing.toAddCommGroup`) are not syntactically the
  field-path ones; `convert` surfaces them as instance-equality goals —
  closable by `rfl`, cheapest via the GaussianIntegral idiom
  (`hasDerivAt_pow` + `.comp` + final `convert … using 1` with `rfl`
  bullets).
* **rw-rule function inference**: passing composition-shaped measurability
  proofs to `lintegral_const_mul`/`integral_pos_iff_support_of_nonneg_ae`
  inside `rw` instantiates the rule with the composition form and the
  rewrite misses; always bind the measurability proof to a `have` with an
  explicitly written lambda type first.
* **`stdNormalPDF` must be unfolded before any pdf-lemma rewrite** (it is
  a def-wrapper over `gaussianPDFReal 0 1`; rw is syntactic).
* `π`/`√`/`ℝ≥0` notations need their `open`s per file (`Real`, scoped
  `NNReal`) — Statement.lean does not open them; qualify instead.

## Go/no-go recommendation

**GO** for continuing the campaign per `blueprint/attack_order.md` — with
the standing caveat that this gates only the *definitional-fidelity*
claim: "the formal Theorem 1.1 statement is non-vacuous and its
definitions carry the paper's meaning; the existence half is proved". Any
public claim of the *uniqueness* theorem still requires the remaining 10
sorries (the genuinely hard analysis: A4/A5, E2, G1/H1, L2 → sorries
#7–#8, #12). Per the plan's M5 kill-switch: nothing external — no Zulip,
no push, no announcement — before an explicit user review.

Schedule note: week-1 Tier-0 goals (0.1, 0.4) are done and 0.3-adjacent
canaries landed early; P1's direct route, budgeted for Tier 3, exists
already. The critical path (N0 → A4 → A5 → …) is unchanged; A4/A5 remain
the long pole.

## Reproduction

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin/kyle-formalization
lake build   # green; exactly 10 "declaration uses 'sorry'" warnings
             # axiom audit prints for every declaration listed above
```

New files: `KyleUniqueness/GaussianHelpers.lean`,
`KyleUniqueness/CondExpBridge.lean`,
`KyleUniqueness/IdentityTheoremSpike.lean`; modified:
`KyleUniqueness/Statement.lean` (4 sorries → proofs, no statement
changed), `KyleUniqueness/AxiomAudit.lean` (new audit entries),
`KyleUniqueness.lean` (umbrella imports). **No line of
`Definitions.lean` was touched.**
