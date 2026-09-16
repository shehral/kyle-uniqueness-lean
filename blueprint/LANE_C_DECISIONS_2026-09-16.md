# Lane-C decisions (2026-09-16) — binding for every proving agent

Shehral delegated all Lane-C statement-review decisions to the agent on 2026-09-16
("make the best judgement calls on my behalf … finish the formalization asap").
These decisions are final for the campaign unless a build-level fact contradicts them.
Paper text: `paper/v4.txt` (v4, 2026-08-20, de-tagged HTML), `paper/v4_alttext.txt`
(math preserved as LaTeX alttext), `paper/v3.txt` (v3). Online: https://arxiv.org/html/2607.23585v4

## D1. Version baseline: v4
New files cite **v4** numbering (Thm 1.1, Prop 4.1, Prop 5.1, Prop 6.1, Thm 7.1,
Lemmas 2.1–2.7 in v4 order, eqs. (2.4)–(2.8), (A.1)) with the v3 label in
parentheses where a blueprint node name refers to it. Existing files keep their
v3 docstrings until the closeout wave re-keys them; see `V4_DELTA_REPORT_2026-09-16.md`.
Crosswalk that matters for the blueprint node names:
- v3 Lemma 2.6 (FOC/W, node B1/B2)      = **v4 Lemma 2.4**, eqs. (2.4) FOC, (2.5) W = φ²F′(φ), (2.6) W′ = φ a.e.; subgradient ineq. = (A.1). The divergence clause v3 (12) is GONE.
- v3 Lemma 4.1 (posterior, D1/D2)       = **v4 Lemma 2.5**, eqs. (2.7) P′ = Cov_{π_y}(id, φ) > 0, (2.8) F′ > 0.
- v3 Lemma 2.4 (resampling, E1)         = **v4 Lemma 2.6** (i)–(iv) verbatim.
- v3 Lemma 2.5 (one-sided Stein)        = DELETED in v4; v4 Lemma 2.7 is Cacoullos (E[f′(V)])² ≤ Var f(V).
- v3 Prop 5 (balance identity, E2)      = **v4 Prop 5.1** (accounting identity) + **v4 Lemma 3.1** (Γ = E[F′(φ(V))]) + Lemma 3.2 (Π Borel).
- v3 Prop 6 (signed root, H1)           = unnumbered construction inside the proof of **v4 Prop 6.1**, with `c := F(0)`.
- v3 Thm 3 (Γ = 1/2, T3)                = **v4 Prop 6.1**. v3 Thm 4 (N2) = **v4 Thm 7.1**. v3 Thm 1 (O1) = **v4 Thm 1.1**.

## D2. Value function W: attainment form (the paper's Π), file `KyleUniqueness/ValueFunction.lean`
```lean
noncomputable def insiderProfit (φ : ℝ → ℝ) (v : ℝ) : ℝ := objective 0 φ v (φ v)
noncomputable abbrev valueFunction := insiderProfit   -- blueprint name W
```
Rationale: total, junk-free, Borel in one line (v4 Lemma 3.2); the literal `⨆ x : ℝ` has junk
value 0 exactly at H1's point `c` where the true value is 0, and costs a 60–120 LOC
measurability detour; `EReal` is the wrong currency for every consumer.
Faithfulness bridge is MANDATORY: `insiderProfit_eq_iSup (h : IsGammaSolution 0 φ) :
insiderProfit φ v = ⨆ x : ℝ, objective 0 φ v x`. Every other B1 lemma carries
`IsGammaSolution 0 φ`. Export nonnegativity, the subgradient inequality (A.1), convexity
(`ConvexOn ℝ Set.univ`), `Monotone φ` (from (A.1) alone), FOC (2.4), (2.5), `StrictMono φ`,
(2.6) as `∀ᵐ v, HasDerivAt (insiderProfit φ) (φ v) v`, and local absolute continuity as the
interval-integral identity `insiderProfit φ b − insiderProfit φ a = ∫ v in a..b, φ v`.
Sanity oracle required: `insiderProfit id = fun v => v ^ 2 / 2` (from `gaussianSmoothing_id`).

## D3. Posterior π_y: a `Measure ℝ` via withDensity, file `KyleUniqueness/Posterior.lean`
`posterior φ y : Measure ℝ := volume.withDensity (fun v => ENNReal.ofReal (stdNormalPDF v * stdNormalPDF (y − φ v) / flowDensity φ y))`
(use the repo's existing density names; check Definitions.lean). Prove `IsProbabilityMeasure`,
`inverseRegression φ y = ∫ v, v ∂posterior φ y`, `id, φ ∈ L²(π_y)`, the covariance form of
`deriv (inverseRegression φ) y` and its strict positivity **under the explicit hypothesis
`StrictMono φ`** (do NOT import ValueFunction — hypotheses decouple the waves), then
D2: `0 < deriv (gaussianSmoothing φ) x` for all x (v4 (2.8)) via the symmetrised
`E[(U₀−U₁)(P(x+U₀)−P(x+U₁))] = 2F′(x)` on γ⊗γ and `measure_prod_diagonal_eq_zero`.
Also prove A1b: the joint law of `(V, Y)` on `stdModel` has density `ϱ(v)ϱ(y − φ v)`.

## D4. Resampling μ₃: flat withDensity on ℝ³, test-function form, file `KyleUniqueness/Resampling.lean`
`resamplingMeasure φ : Measure (ℝ × ℝ × ℝ)` (coordinates `(v₀, v₁, y)`) with density
`ϱ(v₀)ϱ(y−φ v₀) · ϱ(v₁)ϱ(y−φ v₁) / p(y)` — one flat `withDensity`. Prove IsProbabilityMeasure,
(i) invariance under `(v₀,v₁,y) ↦ (v₁,v₀,y)`, (ii) the `(v₁,y)` marginal has density `ϱ(v₁)ϱ(y−φ v₁)`
(state it in density form; do not import Posterior), (iii)/(iv) in **test-function form**:
`∫ v₁ · g(v₀,y) ∂μ₃ = ∫ P(y) · g(v₀,y) ∂μ₃` and `∫ v₁ · g(v₀) ∂μ₃ = ∫ F(φ v₀) · g(v₀) dγ` for
bounded measurable g. No `condExp`. Also the replica identity v4 (5.1):
`Γ = E[(φ(V⁰)−φ(V¹))(V⁰−V¹)]`-type identities to the extent they are pure Tonelli.

## D5. Noise-trader loss identities, file `KyleUniqueness/Loss.lean` (v4 Lemma 3.1 / 3.2)
`noiseTraderLoss φ = ∫ v, deriv (gaussianSmoothing φ) (φ v) ∂γ` (Γ = E[F′(φ(V))]),
with the integrability of `F′(φ(V))`; and `E[U·(P(Y) − V)] = E[U·P(Y)]` (v4's definiens
agrees with the repo's). Π = `insiderProfit` is defined in ValueFunction.lean, not here.

## D6. Route for Γ = E[W(V)] (E2): follow **v4 Prop 5.1** (hypotheses `Monotone φ` and
`0 ≤ Π(V)` a.s.; conclusion `Π(V) ∈ L¹ ∧ Γ = E[Π(V)]`), proof via v4 §5 (truncate φ, replica
identity, three-case sign argument, monotone limit). If the v4 route stalls, the v3 chain
(aₙ-truncation + FOC, blueprint E2) is an acceptable fallback — the consumer only needs
`Γ = E[insiderProfit φ (V)]` and `Integrable`.

## D7. Route for 1 ≤ 2Γ (J1): use the **banked** one-sided Stein inequality
`one_le_sqrt_integral_sq_mul_integral_inv_sq` (SteinInequality.lean) with `f := h` (the
signed root), i.e. v3's route. v4 uses Cacoullos instead; document in the closeout that
SteinInequality.lean is our route, not the paper's current lemma.

## D8. Signed root (H1): follow v4's construction inside Prop 6.1: `c := F(0)`,
`q v := F′(φ v) > 0`, `h v := sign(v − c) · √(2 W v)`, `h′ = 1/√(2q)` a.e.,
`E[h(V)²] = 2Γ`, `E[1/h′(V)²] = 2Γ`. No divergence lemma needed.

## D9. Process
- One new file per node; never edit another node's file in the same wave; never edit
  `Statement.lean`, `AxiomAudit.lean`, `KyleUniqueness.lean` except in the final waves.
- Iterate with `lake env lean KyleUniqueness/<File>.lean`; finish with `lake build KyleUniqueness.<Module>`.
- Standing rules (SETUP.md, attack_order §Standing rules): `export PATH="$HOME/.elan/bin:$PATH"`;
  verify every Mathlib name by grep of `.lake/packages/mathlib` (never from memory);
  `gaussianPDFReal_eval` before pdf rewrites; explicit-lambda measurability `have`s before `rw`;
  lint-clean against `mathlibStandardSet`.
- Git: personal identity (`ali.shehral@gmail.com`), commit after each wave, no assistant footers.
