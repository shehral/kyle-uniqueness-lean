# PROVING_LOG — Kyle-uniqueness formalization, proving campaign

Per-session record of the proving campaign against the v3 statement layer
(paper: Monteiro & Tourky, arXiv:2607.23585 **v3**; toolchain Lean
`v4.32.0`, Mathlib `81a5d257`). Statements themselves are frozen — every
entry below closes a `sorry` under a byte-identical statement, or banks
partial work. **Local only — nothing pushed, posted, or announced.**

---

## Session 1 — 2026-08-12 (Tier 1 + Tier-2 R1 + O1 leg + Q2)

**Result: `lake build` green; sorry count 14 → 2.** All twelve
standard-grade obligations closed in blueprint dependency order; the two
remaining sorries are exactly the two headline uniqueness carriers, both
gated on the §4 machinery (blueprint weeks 3–6). Axiom audit: every proved
declaration `[propext, Classical.choice, Quot.sound]`; the assembled
headline statements inherit `sorryAx` only through the two carriers. Both
canaries re-verified **byte-identical** (statement *and* proof) and
axiom-clean after every close.

### Per-sorry status (numbering = `STATEMENT_NOTES.md` §4 at session start)

| # | Declaration | Node | Status | Proof route |
|---|---|---|---|---|
| 1 | `lemma21_continuous` | A2 | **PROVED** | DCT (`continuous_of_dominated`) for `n` and `p` with dominants `ϱ(0)`, `\|v\|·ϱ(0)`; quotient via `p > 0` |
| 2 | `lemma22_memLp_two` | Q1 | **PROVED** | `MemLp.condExp` L²-contraction of `V ∈ L²` + the proved canary (`P(Y)` is a version) |
| 3 | `lemma23_integrable` | **R1** | **PROVED** | v3 App. A verbatim: `E[\|P(x+U)\|] ≤ E[\|V\|·K_x(φ(V))]` (Tonelli); `K_x` bounded a.s. by the 3-case positive-mass-interval argument (`Ioi`/`Iio`/`δ_x`), complete-the-square kernel `∫ϱ(y−x)ϱ(y−a)/ϱ(y−d) = e^{(x−d)(a−d)}` |
| 4 | `lemma21_unique_continuous_version` | A3 | **PROVED** | flow-a.s. → Lebesgue-a.e. (law identity) + `Continuous.ae_eq_iff_eq` with #1 |
| 5 | `equilibrium_iff_zeroSolution` | O1 leg | **PROVED** | profit = `x(v−F(x))` against ANY pricing rule: a.e.-reduction to the canonical version + `P₀(x+U) ∈ L¹` (from #3, translated) + `E[P₀(x+U)] = F(x)` |
| 6 | `integrable_noiseTraderLoss` | Q1 | **PROVED** | `U ∈ L²`, `P(Y) ∈ L²` (#2), `MemLp.integrable_mul` |
| 7 | `noiseTraderLoss_le_half` | Q1 | **PROVED** | `0 ≤ E[(2M−V−sU)²] = 1+s²−4sΓ` at `s = ±1` (private `integral_sq_kernel'`: 6-term L² expansion + projection identity `E[MV]=E[M²]` via condExp pull-out/tower + moment dictionary) |
| 8 | `noiseTraderLoss_eq_half_iff` | **Q2** | **PROVED** | (⇒) `E[(2M−V−sU)²]=0` ⇒ eq. (16) ⇒ Tonelli sections (`ae_ae_of_ae_prod`) + Gaussian↔Lebesgue null-set transfer + Lebesgue translation invariance ⇒ `φ(v)−sv` a.e.-constant. (⇐) a.e.-affine ⇒ regressions agree pointwise ⇒ `Γ = s/2` by N1/mirror + moments. Both signs via private `noiseTraderLoss_eq_signed_iff` |
| 9 | `noiseTraderLoss_eq_neg_half_iff` | **Q2** | **PROVED** | mirror of #8 (`s = −1`; new private `inverseRegression_neg_affine`) |
| 10 | `isGammaSolution_zero_iff` | N2 | **OPEN** (existence direction **banked**: proved in-file via `gaussianSmoothing_id` + quadratic argmax) | rigidity direction SCHEDULED: needs Theorem 3 (`Γ = 1/2` under (17)) = §4 machinery — B1/B2, D1/D2, E1/**E2**, **H1**, **I1–I3**, J1, T3 — then #8 + N1 + argmax comparison. Weeks 3–6 nodes; none exists yet |
| 11 | `inverseRegression_affine` | N1 | **PROVED** | literal-variance complete-the-square `ϱ(y−v)ϱ(v) = ϱ_{0,2}(y)ϱ_{y/2,1/2}(v)` (new `gaussianPDFReal_mul_gaussianPDFReal_std`, NNReal-mk-free) + Gaussian first moment |
| 12 | `gaussianSmoothing_affine` | N1 | **PROVED** | #11 + `E[U] = 0` |
| 13 | `isEquilibrium_eq_kyleStrategy` | O1 | **OPEN** | SCHEDULED: location–scale reduction to `stdModel` + Theorem 4 (#10). Blocked on the same §4 machinery; all statement-level plumbing it needs beyond that (bridge #5, N1, a.e. machinery, profit finiteness #3) is now proved |
| 14 | `pricingRule_ae_eq_kylePricingRule` | O1 leg | **PROVED** | new order-flow law identity `map (Y_φ) μ = volume.withDensity (ofReal ∘ flowPDF)` (`KyleModel.map_orderFlow`) + everywhere-positive density ⇒ flow-a.s. transfers to Lebesgue-a.e. |

### Assembled statements upgraded to fully-proved (no `sorryAx`)

`eq_kylePricingRule_of_continuous` (last sorried leg was #14),
`inverseRegression_id`, `gaussianSmoothing_id` (leg was #11/#12). Still
inheriting `sorryAx` through #10/#13 only: `kyle_equilibrium_pair_iff`,
`kyle_unique_equilibrium`, `kyle_existsUnique_equilibrium`,
`existsUnique_zeroSolution`.

### Milestones hit (vs. `blueprint/attack_order.md` Gantt)

- **M1** (plan: end wk 1) — N1 + A2 + all of Q1: **done day 1**.
- **M2**'s sorry-#14 half (plan: end wk 2) — `eq_kylePricingRule_of_continuous`
  fully kernel-checked: **done day 1**. (The Stein-file half of M2 remains.)
- **M3**'s demo checkpoint (plan: end wk 4) — `noiseTraderLoss_le_half`,
  the paper's pivot bound, machine-checked: **done day 1**.
- **M4**'s Q2 half (plan: end wk 5–6) — the rigidity equality case
  (Prop 2 eq. (15), both signs): **done day 1**. (E2 remains.)
- R1 (Tier-2 front α, plan wk 3): **done day 1**; unblocks R2's majorant.

### New infrastructure banked (all proved, axiom-clean)

- `GaussianHelpers.lean`: `gaussianPDFReal_std_anti` (monotone in |·|),
  `gaussianPDFReal_std_neg` (evenness), `gaussianPDFReal_std_mul_eq_exp_mul`
  + `lintegral_gaussianPDFReal_std_mul_div` (the `K_x` complete-the-square,
  v3 App. A), `gaussianPDFReal_mul_gaussianPDFReal_std` (σ=τ=1 Kyle
  factorization, NNReal-mk-free), `integral_mul_self_gaussianReal_std`
  (second moment), `ae_volume_of_ae_gaussianReal` (null-set transfer).
- `CondExpBridge.lean`: `KyleModel.measurable_flowPDF`,
  `KyleModel.lintegral_ofReal_kernel_eq_flowPDF`,
  **`KyleModel.map_orderFlow`** (the order-flow law identity — v3 Lemma
  2.1's law clause at general σ; also discharges a piece of blueprint A1),
  `KyleModel.pricingRule_ae_eq_of_flowPDF_pos`, `stdModel_noiseLaw`.
- `Statement.lean` proof-internal privates (not claim surface):
  `flowDensity_ge_Icc`, `exists_Icc_of_Ioi_ne_zero`/`_Iio_`,
  `lintegral_kernel_le_Icc` (R1); `memLp_two_fst'`/`_snd'`, moment
  dictionary, `integral_sq_kernel'` (Prop 2's L² identity);
  `inverseRegression_neg_affine`, `noiseTraderLoss_eq_signed_iff` (Q2).

### File-layout changes (statements untouched)

- Statement.lean: the affine-regression section (4 proved declarations)
  moved above the Proposition-2 section (Q2's ⇐ direction consumes it;
  Lean is order-sensitive). `noiseTraderLoss_le_half`'s proof rewritten to
  consume the shared private `integral_sq_kernel'` (statement identical).
  Two new imports (`ConditionalExpectation.Real`, `.PullOut`) for
  `MemLp.condExp` and the pull-out property.
- Both canaries verified byte-identical (statement + proof) after all
  edits; audit clean.

### Remaining campaign (per blueprint, unchanged)

The two carriers open exactly the planned Tier-2β–Tier-5 path:
**I1–I3** (Stein file, zero project imports — premier upstream candidate),
**R2** (`F ∈ C¹`, majorant now available from R1), **B1/B2** (value
function/FOC), **D1/D2** (posterior C¹/positivity), **E1/E2** (resampling +
balance identity, hard block 3), **H1** (signed root, hard block 4b),
**J1/T3** (glue) → Theorem 3 → #10 → location–scale → #13.

### Reproduction

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd kyle-uniqueness-lean
lake build   # green; exactly 2 "declaration uses 'sorry'" warnings
             # (Statement.lean: isGammaSolution_zero_iff,
             #  isEquilibrium_eq_kyleStrategy)
```

---

## Session 2 — 2026-08-18 (Stein pipeline I1–I3: hard block 2 CLOSED)

**Result: `lake build` green; sorry count unchanged at 2** (the two headline
carriers). **Blueprint nodes I1, I2, I3 — v3 Lemma 2.5, hard block 2 — are
fully proved** in the new file `KyleUniqueness/SteinInequality.lean`
(869 LOC, **zero project imports** — pure Mathlib, the premier upstream
candidate, exactly as planned in `blueprint/attack_order.md` Tier-2 front β).
Axiom audit: all nine new public declarations
`[propext, Classical.choice, Quot.sound]`; file lint-clean (0 warnings).

### Nodes closed

| Node | Declaration(s) | Route |
|---|---|---|
| **I1** | `integral_gaussianPDFReal_stieltjesMeasure` (StieltjesFunction form), `integral_gaussianPDFReal_stieltjesMeasure_of_monotone` | `∫ ϱ dμ_f = E[Z f(Z)]` for bounded monotone `f` by the layer-cake/Tonelli route: center at `f(0)`, split at `z = 0`, `measure_Ioc` turns increments into masses, `lintegral_lintegral_swap` on the explicit product-measurable region, Gaussian tail FTC on **both** tails (`∫_{Ioi t} zϱ = ϱ(t)`, `∫_{Iio t} (−z)ϱ = ϱ(t)`), reassemble via `integral_add_compl`. Monotone form: `Monotone.stieltjesFunction` moves only the countable discontinuity set (`countable_not_continuousAt` + `rightLim` = value at continuity points), Gaussian-null by AC |
| **I2** | `ae_indicator_ofReal_deriv_le_rnDeriv`, `lintegral_indicator_ofReal_deriv_mul_le`, `lintegral_ofReal_deriv_mul_le` | exactly the audit §10-item-6 assembly: `Monotone.ae_hasDerivAt` (a.e. derivative IS `rnDeriv μ_f volume`) + `HasDerivAt.unique` + `ENNReal.ofReal_toReal_le`, then `lintegral_withDensity_eq_lintegral_mul` + **`withDensity_rnDeriv_le`** (the singular part is what the paper's BV citation discards). Stated with an indicator/set parameter so the truncation consumer needs no global derivative for the clamp |
| **truncation** | `ae_hasDerivAt_clamp_of_abs_lt` | on `{|f| < N}` the clamp `max(−N, min(f, N))` is locally `f` at every a.e.-differentiability point (continuity from `HasDerivAt` + `EventuallyEq.hasDerivAt_iff`) — no case analysis at `{f = ±N}` needed |
| **I3** | `one_le_lintegral_sq_mul_lintegral_inv_sq` (ℝ≥0∞ core, **no integrability hypotheses**), `one_le_integral_sq_mul_integral_inv_sq` (Bochner, squared form), `one_le_sqrt_integral_sq_mul_integral_inv_sq` (the paper's outer form of eq. (7)) | per-truncation chain `γ{|f|<N} ≤ (∫⁻1_{S_N}·f′ dγ)^{½}(∫⁻1/f′ dγ)^{½}` (ENNReal Hölder at `HolderConjugate.two_two`) with `∫⁻1_{S_N}·f′ dγ ≤ ∫⁻ϱ dμ_{f_N} = ofReal E[Z f_N(Z)] ≤ (ofReal ∫f_N²)^{½} ≤ A^{½}` (I2 + I1 + Bochner Hölder + `E[Z²]=1`) and `∫⁻1/f′ dγ ≤ B^{½}` (Hölder vs 𝟙); so `γ{|f|<N} ≤ (AB)^{1/4}`; let `N → ∞` by `tendsto_measure_iUnion_atTop` + `le_of_tendsto`, then raise to the 4th rpow. The ℝ≥0∞ core needs **no** case split on `A, B ∈ {0, ∞}` |

### Design notes

- The a.e.-defined derivative `f'` is replaced inside the core by the
  canonical measurable representative `toReal ∘ rnDeriv μ_f volume`
  (`stein_core` private), so the public statements take `f'` with only
  `∀ᵐ HasDerivAt` + positivity — the exact interface H1/J1 will produce.
- The small Gaussian toolkit (density derivative, both tail FTCs, second
  moment via `variance_eq_sub`, `ϱ ≤ (√2π)⁻¹`) is duplicated as `private`
  lemmas from `GaussianHelpers.lean` to keep the file's zero-project-import
  property; the **left** tail FTC and the `atBot` decay are new (not in
  `GaussianHelpers`).
- New audit facts at the pin, load-bearing here: `Real.HolderConjugate`
  (the pin's conjugate-exponent API; `two_two` instance),
  `ENNReal.lintegral_mul_le_Lp_mul_Lq`,
  `integral_mul_le_Lp_mul_Lq_of_nonneg` (Bochner Hölder),
  `StieltjesFunction.isFiniteMeasure_of_forall_abs_le`,
  `ENNReal.continuous_rpow_const` (unconditional),
  `tendsto_measure_iUnion_atTop`, `ENNReal.ofReal_rpow_of_nonneg`.
  Deprecation note: `mul_le_mul_right'` → `mul_le_mul_left` at this pin.

### Milestones (vs. `blueprint/attack_order.md` Gantt)

- **M2's Stein half** (plan: end wk 2 — "hard block 2 dead"): **done.**
  With sorry #14 already closed in session 1, **M2 is now fully hit.**
  Hard-block census: 2 of the v3 plan's surviving hard blocks remain →
  **E2 and H1 only** (I-pipeline retired).

### Node R2 CLOSED (same session, second unit)

**v3 Lemma 2.3's regularity clause — `F ∈ C¹` + eq. (5) — is fully proved**
in the new file `KyleUniqueness/Regularity.lean` (~330 LOC; imports
`Statement` for R1/A2). All eleven public declarations audit to
`[propext, Classical.choice, Quot.sound]`; file lint-clean.

| Declaration | Content |
|---|---|
| `exp_mul_gaussianPDFReal_std` | the shift identity `e^{ct}ϱ(t) = e^{c²/2}ϱ(t−c)` (pure algebra) |
| `abs_mul_gaussianPDFReal_std_le` | `\|t\|ϱ(t) ≤ e^{1/2}(ϱ(t−1)+ϱ(t+1))` via `\|t\| ≤ e^t + e^{−t}` — **no case split, no (1+\|y\|)e^{R\|y\|} bookkeeping**: the blueprint's planned shift-domination simplifies to two applications of the shift identity |
| `gaussianPDFReal_std_shift_le` | `\|s\| ≤ 2 ⇒ ϱ(t−s) ≤ e²(ϱ(t−2)+ϱ(t+2))` |
| `abs_sub_mul_gaussianPDFReal_std_le` | the locally-uniform majorant: `\|x−x₀\| ≤ 1 ⇒ \|y−x\|ϱ(y−x) ≤ 2e^{5/2}(ϱ(y−x₀−2)+ϱ(y−x₀+2))` |
| `gaussianSmoothing_eq_convolution` | eq. (4): `F(x) = ∫ P(y)ϱ(y−x) dy` (via `integral_comp_add_gaussianReal`, banked session 1) |
| `hasDerivAt_gaussianSmoothing` + `integrable_gaussianSmoothing_deriv_kernel` | eq. (5) first form: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` at `𝕜 = ℝ` on `Metric.ball x₀ 1`, majorant integrable by **R1 at `x₀ ± 2`** — exactly the blueprint route, complex analysis nowhere |
| `deriv_gaussianSmoothing_eq_prob` | eq. (5) second form `F′(x) = E[U·P(x+U)]` (translation invariance; hypothesis-free) |
| `continuous_gaussianSmoothing_deriv`, `deriv_gaussianSmoothing`, `continuous_deriv_gaussianSmoothing` | `F′` continuous (`continuousAt_of_dominated`, same majorant) ⇒ `F ∈ C¹` |

Deferred (logged, not blocked): Lemma 2.3's bookkeeping clause
`F(φ(V)) = E[E[V∣Y]∣V]` a.s. — it is E2's input and belongs with the
resampling file's condExp plumbing (E1), not with the analytic node.

### Node D1, C¹ legs BANKED (same session, third unit)

New file `KyleUniqueness/PosteriorDeriv.lean` (~180 LOC, imports
`Regularity`): the differentiation-under-the-integral legs of v3 Lemma 4.1,
all proved and axiom-clean —
`abs_mul_gaussianPDFReal_std_le_const` (`|t|ϱ(t) ≤ 2e^{1/2}(√2π)⁻¹`,
the uniform kernel bound), `hasDerivAt_flowDensity`
(`p′(y) = −E[(y−φV)ϱ(y−φV)]`), `hasDerivAt_flowNumerator`
(`n′(y) = −E[V(y−φV)ϱ(y−φV)]`), and `hasDerivAt_inverseRegression`
(`P = n/p` differentiable, quotient formula; `p > 0` from Lemma 2.1).
Dominants are constant resp. `|v|`-linear against the Gaussian prior —
no ball-shifted majorant needed on this side. **D1's remaining
obligations** (the covariance form `P′(y) = Cov_{π_y}(id, φ)`, its strict
positivity, and D2) are gated on B2's strict monotonicity and the `π_y`
statement review.

### Remaining campaign (frontier update)

Critical path now: **B1/B2** (value function / FOC — NOTE: the
attainment-form definition of `W` is a Lane-C statement-review item per
`attack_order.md` §1; no review is on record, so the next session should
either surface a proposed `W` definition for review or draft it with the
review flagged) → D1/D2 → E1/**E2** → **H1** → J1/T3 → Theorem 3 →
carrier #10 → location–scale → carrier #13. D1's `C¹`-legs
(differentiation of `n`, `p` under the integral) are now cheap with the
banked majorant toolkit (constant/linear dominants against the Gaussian
prior suffice); D1's positivity leg and D2 wait on B2's strict
monotonicity. J1's Stein application is fully unblocked on the I-side
(consume `one_le_integral_sq_mul_integral_inv_sq` with `f := h`, the H1
signed root, under the `E[h²] = E[1/h′²] = 2Γ` dictionary).

### Reproduction

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd kyle-uniqueness-lean
lake build   # green; exactly 2 "declaration uses 'sorry'" warnings
             # (Statement.lean: isGammaSolution_zero_iff,
             #  isEquilibrium_eq_kyleStrategy); AxiomAudit prints the 9
             # Stein declarations with [propext, Classical.choice, Quot.sound]
```

---

## Session 3 — 2026-09-16, Wave 1 (Fable orchestrator; opus provers + adversarial verifiers): B1, B2, A1b, D1-rest, D2, E1, R2b, Lemma 3.1/3.2 CLOSED

**Context:** arXiv v4 (2026-08-20) found to be a proof rewrite (see the crosswalk in `STATEMENT_NOTES.md` §1); all Lane-C decisions delegated to the agent and recorded in `blueprint/LANE_C_DECISIONS_2026-09-16.md`. New files cite v4 numbering.

**Result:** four new modules, 2,509 LOC, **0 sorries**, every public declaration `[propext, Classical.choice, Quot.sound]`, lint-clean, each `lake build KyleUniqueness.<M>` green. Each module was independently verified by an adversarial agent (build from deleted oleans, out-of-tree `#print axioms`, statement-by-statement faithfulness vs `paper/v4.txt`, vacuity probes at φ = id); all four passed on the first round. Umbrella import + AxiomAudit wiring deferred to closeout by rule D9.

| Module | LOC | Nodes | Headline declarations |
|---|---|---|---|
| `ValueFunction.lean` | 391 | B1+B2 (v4 Lemma 2.4, (A.1), (2.4)-(2.6)) | `insiderProfit`, `valueFunction`, `objective_zero`, `insiderProfit_apply`, `isMaxOn_objective`, `objective_le_insiderProfit`, `insiderProfit_eq_iSup`, `continuous_gaussianSmoothing`, `measurable_insiderProfit`, `insiderProfit_nonneg`, `insiderProfit_subgradient`, `insiderProfit_sub_sandwich` … |
| `Posterior.lean` | 865 | A1b + D1-rest + D2 (v4 Lemma 2.1, §2.2 π_y, Lemma 2.5 (2.7)-(2.8)) | `map_value_orderFlow`, `stdModel_map_value_orderFlow`, `jointDensity`, `measurable_jointDensity`, `posteriorDensity`, `posterior`, `isProbabilityMeasure_posterior`, `nullSingletonClass_posterior`, `integral_posterior`, `integrable_posterior_iff`, `inverseRegression_eq_integral_posterior`, `memLp_id_posterior` … |
| `Resampling.lean` | 970 | E1 + R2b (v4 Lemma 2.6 (i)-(iv), Lemma 2.3 tower clause) | `resamplingMeasure`, `isProbabilityMeasure_resamplingMeasure`, `resamplingMeasure_map_swap`, `resamplingMeasure_map_snd`, `resamplingMeasure_map_fst`, `resamplingMeasure_map_v1`, `resamplingMeasure_map_v0`, `resamplingMeasure_map_y`, `integrable_v1_resampling`, `integrable_v0_resampling`, `integrable_inverseRegression_resampling`, `integrable_bayesNumerator_kernel` … |
| `Loss.lean` | 283 | v4 Lemma 3.1 / 3.2 (Γ = E[F′(φ(V))], definiens agreement) | `deriv_gaussianSmoothing_eq_integral`, `deriv_gaussianSmoothing_comp_eq`, `integrable_deriv_gaussianSmoothing_comp`, `noiseTraderLoss_eq_integral_deriv`, `integral_snd_mul_sub_fst_eq_noiseTraderLoss`, `integral_noise_mul_sub_value_eq_noiseTraderLoss`, `covariance_noise_condExp_eq_noiseTraderLoss`, `integrable_inverseRegression_const_add`, `expectedProfit_inverseRegression`, `objective_eq_expectedProfit`, `noiseTraderLoss_id` … |

### ValueFunction.lean — route
All 14 requested deliverables are proved, plus 5 auxiliary public exports and 2 private helpers. Definitions are exactly decision D2. Two private lemmas: `slope_insiderProfit_mem` (slope squeeze), `rightLim_mul_le_sub` (one-sided upgrade of (A.1)).

ROUTES ACTUALLY USED (all verified by grep against .lake/packages/mathlib before use):
- (A.1) `insiderProfit_subgradient`: one application of `h.2 w (φ v)` — the order `φ v` is admissible at `w`; `W v + φ v (w−v) = φ v (w − F(φ v)) = objective 0 φ w (φ v)`. Everything downstream except FOC/(2.5) is a consequence of this one inequality.
- (2) iSup bridge: `le_antisymm (le_ciSup hb (φ v)) (ciSup_le …)` with `BddAbove (Set.range (objective 0 φ v))` witnessed by the attained value.
- (6) convexity: NOT via "sup of affine"; directly from (A.1) at the convex combination, after `obtain rfl : b = 1 - a` so `nlinarith` sees a pure polynomial identity (keeping `b` symbolic makes the `(a+b)·W z = W z` step nonlinear and nlinarith flakes).
- (8) FOC: `(isMaxOn_objective h v).isLocalMax Filter.univ_mem` then `IsLocalMax.hasDerivAt_eq_zero` (exact name; `IsLocalMax.deriv_eq_zero` also exists). The `HasDerivAt` for `x ↦ x(v − F x)` is `(hasDerivAt_id _).mul (hF.const_sub v)` where `hF` is `hasDerivAt_gaussianSmoothing` re-stated at `deriv` via `deriv_gaussianSmoothing`.
- (11) continuity: `ConvexOn.continuousOn isOpen_univ` (Mathlib/Analysis/Convex/Continuous.lean, needs `[FiniteDimensional ℝ E]`; ℝ qualifies) + `← continuousOn_univ`. This replaces the paper's Rockafellar citation; no Lipschitz bookkeeping needed.
- (12) a.e. derivative: `hasDerivAt_iff_tendsto_slope` + `tendsto_of_tendsto_of_tendsto_of_le_of_le'` squeezing `slope W v w` between `min (φ v) (φ w)` and `max (φ v) (φ w)` (this two-sided form works uniformly for `w < v` and `w > v`, unlike a one-sided bound), then `Monotone.countable_not_continuousAt` + `Set.Countable.ae_notMem volume`.
- (13) FTC: `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` (NOTE: at this pin it wants `HasDerivWithinAt f (f' x) (Ioi x) x`, not `Ici`). The right derivative is `Function.rightLim φ`, NOT `φ` — at a jump point of φ the right derivative strictly exceeds `φ v`, so the `Ici/Ioi` FTC cannot be fed `φ` directly. `rightLim φ` is monotone (`Monotone.rightLim`) hence `Monotone.intervalIntegrable`, and equals `φ` off the countable discontinuity set (`Monotone.continuousWithinAt_Ioi_iff_rightLim_eq`), so `intervalIntegral.integral_congr_ae` converts the integrand. The `b < a` case goes through `intervalIntegral.integral_symm`. The lower bound `rightLim φ v · (w−v) ≤ W w − W v` needs a genuine limit: (A.1) at interior `u ∈ (v,w)` plus `le_of_tendsto` along `𝓝[>] v` (`Ioo_mem_nhdsGT`); `𝓝[>] v` is `NeBot` by the `nhdsGT_neBot` instance.
- Imports added beyond `KyleUniqueness.Regularity`: `Mathlib.Analysis.Convex.Continuous`, `Mathlib.Analysis.Calculus.Deriv.Slope`, `Mathlib.Analysis.Calculus.LocalExtr.Basic`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.

NO HYPOTHESIS BEYOND THE PAPER'S was added anywhere. `measurable_insiderProfit` and `insiderProfit_id` need no `IsGammaSolution` at all, as specified.

VERIFICATION PERFORMED:
- `lake build KyleUniqueness.ValueFunction` green from a deleted olean (1.7s; "Build completed successfully (3123 jobs)").
- Lint-clean: `lake env lean -Dweak.linter.mathlibStandardSet=true -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false KyleUniqueness/ValueFunction.lean` prints nothing (control: Regularity.lean prints its pre-existing `ring`→`ring_nf` info, so the linters are demonstrably firing).
- `#print axioms` on all 24 public declarations: every one `[propext, Classical.choice, Quot.sound]` (run in a temporary section, since deleted).
- END-TO-END SMOKE TEST (temporary, since deleted): with a locally reproved `IsGammaSolution 0 id`, the chain yields `b^2/2 − a^2/2 = ∫ v in a..b, v` (the classical oracle, through the rightLim/FTC route), `StrictMono id`, `v^2/2 = ⨆ x, objective 0 id v x`, the FOC at `φ = id`, and `ConvexOn ℝ univ (fun v => v^2/2)`. All five compiled. This also demonstrates the `IsGammaSolution 0 φ` hypothesis is non-vacuous, so none of the 12 hypothesised theorems is vacuously true.

NOT DONE (per instructions): the module is NOT added to `KyleUniqueness.lean` or `AxiomAudit.lean` (rule 1 forbids editing them). The closeout wave must add `import KyleUniqueness.ValueFunction` to both, and the 24 `#print axioms` lines to AxiomAudit. Until then the module is a leaf and only builds via the explicit target `lake build KyleUniqueness.ValueFunction`.

**Gotchas (pin-specific):**
Pin-specific facts worth banking in PROVING_LOG.md:

1. `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` at this pin takes `HasDerivWithinAt f (f' x) (Ioi x) x` (NOT `Ici x`, which older Mathlib docs and the task brief both say). `hasDerivWithinAt_Ioi_iff_Ici` exists if the other form is ever needed.
2. There is NO countable-exceptional-set FTC in this pin's `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`. The `rightLim` detour is mandatory, not a stylistic choice — `W` genuinely fails to have `φ v` as its right derivative at jump points of `φ`, so any attempt to feed `φ` to the FTC directly is unsound, not merely hard.
3. `squeeze_zero_norm` does NOT exist at this pin (only `squeeze_zero` / `squeeze_zero'`). The min/max two-sided squeeze via `tendsto_of_tendsto_of_tendsto_of_le_of_le'` is cleaner anyway and avoids all `abs` bookkeeping.
4. `hw.lt_or_lt` on `hw : w ≠ v` fails — the elaborator unfolds `Ne` to `w = v → False` and then looks for `Function.lt_or_lt`. Use `lt_or_gt_of_ne hw`.
5. `continuous_const.min continuous_id` cannot infer the constant when used inline inside `Tendsto.comp`; bind it first as `have hcmin : Continuous fun y : ℝ => min (φ v) y := continuous_const.min continuous_id`.
6. `hasDerivAt_const c v |>.sub hF` produces the function `(fun _ => c) - F` (pointwise-sub of functions) with derivative `0 - F'`, which does not defeq-match `fun x => c - F x` with derivative `-F'`. Use `HasDerivAt.const_sub` instead.
7. `simp only [insiderProfit_apply]` makes no progress on the unapplied goal `Measurable (insiderProfit φ)`; rewrite with `funext (insiderProfit_apply φ)` first.
8. Division lemma names at this pin: `le_div_iff₀` / `div_le_iff₀` (positive denominator) and `le_div_iff_of_neg` / `div_le_iff_of_neg` (negative). The `₀` suffix is required; unsuffixed `le_div_iff` is gone.
9. `lake env lean <file>` does NOT pick up the lakefile's `leanOptions`, so it does not run `weak.linter.mathlibStandardSet`. Lint-clean claims must come from `lake build <module>` or from `lake env lean -Dweak.linter.mathlibStandardSet=true …`.
10. In `convexOn_insiderProfit`, keeping `b` symbolic (rather than `obtain rfl : b = 1 - a`) leaves `nlinarith` needing to multiply `hab : a + b = 1` by the atom `W z` — a nonlinear step it does not reliably find. Substituting `b` first makes the whole thing a ring identity.
11. `Set.Countable.ae_notMem` lives in `Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean` and needs `[NullSingletonClass μ]` (the pin's name; `NoAtoms` is gone, as the standing rules already note). `volume` on ℝ has the instance.

### Posterior.lean — route
All 7 deliverables landed; 67 public declarations, 0 sorries, lint-clean under the package's `weak.linter.mathlibStandardSet`, `lake build KyleUniqueness.Posterior` green (3124 jobs), and all 67 `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

ROUTES ACTUALLY TAKEN

1. A1b (`map_value_orderFlow`): direct `Measure.ext`, mirroring `KyleModel.map_orderFlow`'s style. For measurable `s`: `Measure.prod_apply` → per-slice `lintegral_indicator_one` + `lintegral_comp_add_gaussianReal'` (the banked shift) → outer `gaussianReal_of_var_ne_zero` + `lintegral_withDensity_eq_lintegral_mul` → `Measure.volume_eq_prod ℝ ℝ` + Tonelli (`lintegral_prod`). Mathlib's group-shear measure-preservation lemmas do NOT apply (our shear is by an arbitrary Borel φ, not the group operation), so the direct computation is the route. Also exported in `stdModel` packaging (definitionally the same term).

2. `posterior` is the flat `volume.withDensity (ofReal (ϱ v · ϱ(y−φ v) / p_Y y))` of decision D3. The load-bearing piece is the *unconditional* transfer lemma `integral_posterior` (no hypothesis on `g`: `integral_withDensity_eq_integral_toReal_smul` holds with both sides undefined), plus `integrable_posterior_iff` (`integrable_withDensity_iff_integrable_smul'`). Everything downstream goes through these two.

3. L² clauses: proved via `memLp_two_iff_integrable_sq` + `integrable_posterior_iff` + `Integrable.mono'`. Needed one new kernel bound not in the repo: `sq_mul_stdNormalPDF_le_const : t²ϱ(t) ≤ 2e²(2π)^{-1/2}`, proved by `|t| ≤ e^{|t|}` ⟹ `t² ≤ e^{2|t|} ≤ e^{2t}+e^{−2t}`, then Regularity's `exp_mul_gaussianPDFReal_std` at c = ±2. From it, `sq_strategy_mul_kernel_le` is the paper's `(y−t)²ϱ(t) ≤ 2M²ϱ(t)+2t²ϱ(t)` bound verbatim.

4. (2.7): exactly the prescribed route. `(hasDerivAt_inverseRegression hφ y).deriv` gives `(n'p − np')/p²`; `integral_flowNumerator_deriv_kernel` / `integral_flowDensity_deriv_kernel` split `n' = −y·n + E[Vφϱ]`, `p' = −y·p + E[φϱ]`; three `integral_posterior` rewrites; `field_simp; ring`. The `y·n`/`y·p` terms cancel exactly as predicted.

5/6/7: I factored the symmetrisation into three measure-generic lemmas (`integrable_symm`, `integral_symm_eq`, `integral_symm_pos`) over an arbitrary probability measure on ℝ, then instantiated twice — at `π_y` with `g := φ` for (2.7), and at `γ` with `g := u ↦ P(x+u)` for (2.8). This is a deliberate simplification over writing the 4-term product split twice. `integral_symm_pos` bundles nonnegativity + `integral_pos_iff_support_of_nonneg_ae` + `support = diagonalᶜ` + `measure_prod_diagonal_eq_zero` + `measure_compl`; it needs only `[IsProbabilityMeasure μ] [NullSingletonClass μ]`. π_y's atomlessness comes free from `NullSingletonClass.withDensity` (registered as an instance here); γ's was already registered in GaussianHelpers.

For (2.8) the two γ-integrability inputs are the banked Lebesgue statements translated by x: `lemma23_integrable` and `integrable_gaussianSmoothing_deriv_kernel`, each pushed through `Integrable.comp_add_left` (volume is add-left-invariant) and `integrable_gaussianReal_iff`. `E[U]=0` is `integral_id_gaussianReal`.

SANITY ORACLES RUN (scratch file, all typecheck): at φ = id the covariance form evaluates to exactly 1/2 = Var(N(y/2, 1/2)) (cross-checked against the banked `inverseRegression_id`); `deriv (gaussianSmoothing id) = 1/2` from `gaussianSmoothing_id`, and `deriv_gaussianSmoothing_pos_of_strictMono measurable_id strictMono_id` applies. Sign conventions confirmed independently of the proofs.

CONSUMER INTERFACE FOR THE NEXT WAVES
- `isProbabilityMeasure_posterior` is a THEOREM, not an instance (hφ is not inferable). Consumers must `haveI := isProbabilityMeasure_posterior hφ y` before anything needing `IsProbabilityMeasure (posterior φ y)`. `nullSingletonClass_posterior` IS an instance.
- ValueFunction's wave should consume `deriv_gaussianSmoothing_pos_of_strictMono` / `strictMono_gaussianSmoothing_of_strictMono` (StrictMono φ front) or, if it only has `StrictMono P`, the `hP`-fronted `deriv_gaussianSmoothing_pos` / `strictMono_gaussianSmoothing`.
- Resampling (D4) may want `map_value_orderFlow` / `jointDensity` and `integral_posterior`; note the decisions file says Resampling should state its marginal in density form and not import Posterior — `jointDensity` is nonetheless available if that changes.
- `integral_symm_eq` / `integral_symm_pos` are measure-generic and reusable (e.g. for the replica identity v4 (5.1)).

**Gotchas (pin-specific):**
Reusable facts for the other agents / later waves at this pin:

1. `Integrable.neg`, `.sub`, `.add` produce `Pi`-level functions (`-f`, `f - g`), and `rw [integral_add h1 h2]` / `integral_sub` then FAIL to match a goal written with explicit lambdas. Fix: always bind an intermediate `have hk : Integrable (fun v => <explicit lambda>) μ := h1.sub h2` and pass `hk`. This bit me three times (`integral_flowDensity_deriv_kernel`, `integral_flowNumerator_deriv_kernel`, `deriv_inverseRegression_eq_symm`).

2. `rw [smul_eq_mul, ...]` after `integral_withDensity_eq_integral_toReal_smul` needs a `beta_reduce` first — the goal is a beta-redex `(fun x => …) v` and `rw` will not see through it. Same for `integrable_congr`.

3. `gcongr` splits `a * b + c * d ≤ a' * b' + c' * d'` factor-by-factor in an order that does not match the obvious bullet list; two of my three uses produced mismatched goals. Explicit `add_le_add (mul_le_mul_of_nonneg_left …) …` terms are more robust here.

4. `volume_eq_prod` is `MeasureTheory.Measure.volume_eq_prod` (namespace `Measure`, takes the two types explicitly: `Measure.volume_eq_prod ℝ ℝ`). Bare `volume_eq_prod` is an unknown identifier even with `open MeasureTheory`.

5. `mul_nonneg_of_nonpos_of_nonpos` (not `mul_nonneg_of_nonpos_nonpos`) is the name at this pin. `abs_sub a b : |a - b| ≤ |a| + |b|` does exist (it is NOT `abs_sub_comm`).

6. `stdNormalPDF` is a `noncomputable def` for `gaussianPDFReal 0 1`, so `exact`/`le_trans` unify across the two spellings but `rw`/`simp`/`ring` do not. I added `stdNormalPDF`-spelled aliases (`stdNormalPDF_nonneg/_pos/_le`, `measurable_stdNormalPDF`, `abs_mul_stdNormalPDF_le_const`, `exp_mul_stdNormalPDF`) once at the top; recommend other files do the same rather than sprinkling `rw [stdNormalPDF]`. Note `simpa using gaussianPDFReal_le 0 1 t` does NOT prove the `stdNormalPDF` form — simp normalises the RHS but leaves the LHS head unfolded; you need `rw [stdNormalPDF]` first.

7. `positivity` cannot see that `stdNormalPDF t ≥ 0` (opaque def), so every nonnegativity side-goal involving ϱ needs an explicit `mul_nonneg (stdNormalPDF_nonneg _) …`.

8. `MemLp.integrable_mul` at this pin takes `[ENNReal.HolderTriple p q 1]`; `HolderTriple 2 2 1` resolves by `infer_instance`, so `hf.integrable_mul hg : Integrable (f * g) μ` works for two `MemLp _ 2` hypotheses with no extra argument.

9. `memLp_two_iff_integrable_sq aestronglyMeasurable_id` forces `f := id`, so the resulting goal carries `id x ^ 2`; either state the MemLp lemma with `id` (what I did) or add `id_eq` to the closing `simp only`.

10. `integral_prod_mul` and `integral_withDensity_eq_integral_smul` are both UNCONDITIONAL (they hold with both sides undefined), which is what makes `integral_posterior` and `integral_symm_eq` hypothesis-light. Don't hunt for integrability side conditions on them.

11. `Integrable.comp_add_left` exists (to_additive of `Integrable.comp_mul_left`, in `MeasureTheory/Group/Integral.lean`) and applies to `volume` on ℝ — it is the clean way to translate a Lebesgue-integrability statement by a constant. Grepping for its own name finds nothing; grep `comp_mul_left`.

12. The standing rule about `gaussianPDFReal_eval` never bit me because I never unfolded ϱ to its `exp` form — all bounds route through the banked `gaussianPDFReal_le`, `exp_mul_gaussianPDFReal_std`, `abs_mul_gaussianPDFReal_std_le_const`. Recommend the same discipline elsewhere: the `NNReal.mk` coercion trap only appears if you unfold.

13. `lake env lean <file>` does NOT apply the package's `leanOptions`, so it does not run the `mathlibStandardSet` linter. To lint-check without a full build: `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true <file>`.

14. Pre-existing noise in the tree (not from this file): `lake build` replays two `sorry` warnings from `Statement.lean` (lines 1283, 1339) and an `info: ring failed / Try this: ring_nf` from `Regularity.lean:57`. Don't chase those when checking a new module's cleanliness.

### Resampling.lean — route
ROUTE (D4 as written, no deviations). resamplingMeasure φ = one flat `volume.withDensity` on ℝ³ with the literal density from the task spec. Everything reduces to two private master Tonelli identities, `lintegral_resampling_v0/v1`, which put ∫⁻ f dμ₃ into iterated form (y outer; v₀ resp. v₁ innermost) via `Measure.volume_eq_prod ℝ (ℝ×ℝ)` + `lintegral_prod_symm'` twice, plus `lintegral_lintegral_swap` for the inner transposition. Those in turn consume exactly two 1-D kernel integrals: ∫ ϱ(v)ϱ(y−φv) dv = p(y) (= `flowDensity` transported from `gaussianReal` to flat Lebesgue by `integral_gaussianReal_eq_integral_smul`) and ∫ ϱ(v)ϱ(y−φv) dy = ϱ(v).

(i) EXCHANGEABILITY: no MeasurePreserving / prodAssoc dance was needed. `Measure.ext_of_lintegral` + `lintegral_map`, then master-v1 on the composed test function vs master-v0 on the plain one: the two iterated forms are alpha-variants differing only by `rd (v₀,v₁,y)` vs `rd (v₁,v₀,y)`, closed by `mul_comm`. ~15 lines instead of the ~80 the prodAssoc/swap route would cost.

(ii) MARGINALS: same `Measure.ext_of_lintegral` pattern; the v₀ (resp. v₁) integral of the density is the joint density by `lintegral_ofReal_rd_v0/v1`, and the target withDensity is unfolded by a private `lintegral_joint_withDensity` (one `lintegral_prod_symm'`). Stated in density form exactly as specified; `Posterior.lean` is NOT imported.

BONUS 1-D marginals (`resamplingMeasure_map_v0/v1/y`) were added because they buy the integrability deliverables almost free: V⁰,V¹ ~ N(0,1) under μ₃ gives `integrable_v0/v1_resampling` from `integrable_id_gaussianReal` via `Integrable.comp_measurable`, and MemLp-2 via `memLp_map_measure_iff` gives `integrable_v0_mul_v1_resampling` from `MemLp.integrable_mul`. `map (·.2.2) μ₃ = withDensity p = map (orderFlow φ) stdModel.μ` (using `KyleModel.map_orderFlow` + `stdModel_flowPDF`) turns `lemma22_memLp_two` into `integrable_inverseRegression_resampling` in ~10 lines — this replaced a planned ~40-line Tonelli bound on ∫|n(y)|dy.

(iii): `integral_withDensity_eq_integral_toReal_smul` to move to flat volume, `integrable_withDensity_iff` to move integrability the same way, then a private Bochner Fubini `integral_triple_v1` (order v₀, y, v₁) built from `integral_prod` + `integral_prod_symm` + `Integrable.prod_right_ae`. The innermost v₁-integral of both sides collapses to the SAME value `ϱ(v₀)ϱ(y−φv₀)·P(y)·g(v₀,y)` (private `integral_rd_v1_id` / `integral_rd_v1_const`), so no back-transformation is needed — two `integral_congr_ae`s finish it.

(iv): (iii) with g' := g ∘ fst, then `integral_map` onto the (v₀,y) marginal (= (ii)), `integral_pair` (2-D Fubini, v outer), and the inner y-integral is `gaussianSmoothing_eq_convolution hφ (φ v)` from Regularity.lean. Finally `integral_gaussianReal_eq_integral_smul` to land on ∂γ.

Deliverable 6: `integral_v1_mul_comp_eq_gaussianSmoothing` is (iv) at g := k ∘ φ (one line). `integral_v0_mul_v1_resampling` (E[V⁰V¹] = E[P(Y)²]) turned out cheap after all: the |v₀v₁| ≤ (v₀²+v₁²)/2 bound was never needed because both replicas are standard normal under μ₃, so MemLp-2 × MemLp-2 gives integrability directly; the identity uses a second Bochner Fubini `integral_triple_v0` (order y, v₁, v₀) plus `rd_symm`. NO Cauchy–Schwarz anywhere.

Deliverable 7 (R2b) WAS cheap and is DONE, but not by the route I first planned. Instead of needing the joint law of (V,Y) on stdModel (that is D3's A1b, not yet on disk), the set-integral identity over σ(V)-sets is a plain Fubini on γ⊗γ: ∫ 1_A(ω.1)·P(φω.1+ω.2) d(γ⊗γ) = ∫ 1_A(v)·(∫ P(φ v+u) dγ(u)) dγ(v), and the inner integral IS `gaussianSmoothing φ (φ v)` BY DEFINITION (rfl). Integrability of F∘φ then falls out of `Integrable.integral_prod_left` applied to `lemma22_memLp_two`, giving the public `integrable_gaussianSmoothing_comp`. Assembly is `ae_eq_condExp_of_forall_setIntegral_eq` (CondExpBridge's `isPricingRule_of_forall_mul_flowPDF` pattern, incl. the `rintro s ⟨A, hA, rfl⟩` comap destructuring) then `.trans (condExp_congr_ae (lemma21_isPricingRule hφ).ae_eq_condExp)` to convert P(Y) into E[V|Y] inside the outer condExp.

One unused private lemma (`integrable_id_mul_jd`) was found by a dead-code scan and exported instead of deleted, as `integrable_bayesNumerator_kernel` / `integral_bayesNumerator_kernel` — it certifies that ∫ v·ϱ(v)ϱ(y−φv) dv is a genuine (non-junk) Bochner integral, i.e. that the identities are not vacuous. Useful for D3.

44 private helpers, 20 public declarations, no unused privates.

**Gotchas (pin-specific):**
TOOLCHAIN / PROCESS
1. **`lake env lean <file>` does NOT run the style linters; `lake build <module>` does.** The lakefile puts `weak.linter.mathlibStandardSet` in `leanOptions`, which `lake env lean` never sees. I had a file that was warning-free under `lake env lean` for the whole session and then produced five `linter.style.show` warnings on the first `lake build`. Iterate with `lake env lean` for speed, but you are NOT lint-clean until `lake build KyleUniqueness.<Module>` says so. Budget a pass for it.
2. The linter in question: a `show` TACTIC that actually changes the goal (even only up to defeq/delta) must be `change`. Term-level `show ... from ...` is fine and is not flagged.
3. `linter.style.longLine` is apparently NOT in `mathlibStandardSet` at this pin — 110-char lines built clean. I wrapped everything to ≤ 99 anyway; do the same in case the closeout wave turns it on.

LEAN / MATHLIB AT THIS PIN
4. **`isDefEq` heartbeat blowups come from `Measurable.comp` against a lambda goal.** `(measurable_jd hφ).comp (measurable_fst.prodMk measurable_snd.snd)` produced `Measurable (f ∘ g)` and unifying that with `Measurable fun q => jd φ q.1 q.2.2` timed out at 200000 heartbeats (twice, in different lemmas). FIX: state the measurability helper in *composition-general* form from the start — `measurable_jd (ha : Measurable a) (hb : Measurable b) : Measurable fun x => jd φ (a x) (b x)` — and instantiate. No `maxHeartbeats` bump was needed anywhere in the file.
5. Same family of problem, milder: passing `hf.comp hg` straight into a lemma assigns the metavariable to `f ∘ g` and the subsequent `rw` then fails to find the pattern (it wants `fun a => f (a.2.1, a.1, a.2.2)`). Always bind the composed measurability to an explicit-lambda `have` first. This is the standing rule in attack_order.md §Standing rules and it bit me four times.
6. `lintegral_prod_symm'` / `lintegral_prod` need `(μ := ...) (ν := ...)` given EXPLICITLY when the ambient measure is `volume` on a nested product; without them the same `isDefEq` timeout appears. The identical proof in a standalone scratch file (only Mathlib imported) elaborated in 1.5 s with implicits — the blowup is import-context-sensitive, so a scratch-file sanity check can mislead you.
7. `Measurable.mul` concludes `Measurable (f * g)` (Pi.mul), NOT `Measurable fun x => f x * g x`. `rw [lintegral_const_mul _ h]` then fails with a `(… * …) a` pattern. Either bind to an explicit-lambda `have` (defeq closes it) or use `Measurable.fun_mul`.
8. `measurable_id : Measurable id` leaves `id x` un-beta-reduced in the higher-order-unified conclusion, which breaks later `rw`s. Wrap once: `lemma measurable_jd_left ... : Measurable fun v => jd φ v y := by exact measurable_jd hφ measurable_id measurable_const` — the `by exact` forces the ascribed clean statement.
9. `rw [stdNormalPDF]` works (it is a point-free `def`), but `rw` replaces ALL occurrences, so `rw [stdNormalPDF, stdNormalPDF]` fails with "Failed to rewrite using equation theorems". Same trap for `rw [← hmapfst]` where `hmapfst : map Prod.fst (γ.prod γ) = γ`: the backwards rewrite hits the `gaussianReal 0 1`s inside the product measure too and produces `(map Prod.fst (γ.prod γ)).prod (map Prod.fst (γ.prod γ))`. Use `have h := integral_map …; rw [hmapfst] at h; exact h.symm` instead.
10. After `integral_prod` / `lintegral_triple_*` / `integral_congr_ae`, goals carry unreduced projections like `f ((v₀,v₁,y).2.1, (v₀,v₁,y).2.2)`. A bare `dsimp only` fixes them; without it every subsequent `rw` misses. Needed in six places.
11. To fold an explicit density expression back into a private abbreviation, add a *reversed* rfl-lemma `jd_apply : ϱ v * ϱ (y − φ v) = jd φ v y := rfl` and `simp only [jd_apply]`. Public statements then quote the explicit form (so they stay usable without the private def) while the proofs work with the abbreviation.
12. `field_simp` frequently closes these goals outright, so a trailing `ring` errors with "No goals to be solved". Conversely the `a * b / p * c = a / p * c * b` rearrangements need NO `field_simp` at all — plain `ring` handles `/` in a `DivisionRing`. I removed two `field_simp`s and two `ring`s on this account.
13. `Integrable.integral_prod_left` integrates the SECOND variable (`fun x => ∫ y, f (x,y)`); the one that integrates the first is `Integrable.integral_prod_right`. Easy to pick the wrong one when reshuffling a triple product.
14. `Measurable.stronglyMeasurable` has no `(m := …)` named argument at this pin. To get `AEStronglyMeasurable[m]` for a comap σ-algebra, bind `have hmeas : Measurable[MeasurableSpace.comap …] fun ω => …  := hFmeas.comp (Measurable.of_comap_le le_rfl)` first, then `hmeas.stronglyMeasurable.aestronglyMeasurable`.
15. `Measure.ext_of_lintegral ν (∀ f, Measurable f → ∫⁻ f ∂μ = ∫⁻ f ∂ν)` is far more pleasant than `Measure.ext` + indicator gymnastics for every `Measure.map … = …` statement here. It is the single highest-leverage lemma in this file.
16. Note `(q.2.1, q.2.2)` is NOT syntactically `q.2` even though structure eta makes them defeq — state map lemmas exactly as the consumer will write them.

MATHEMATICAL
17. The `E[V⁰V¹] = E[P(Y)²]` integrability does NOT need Cauchy–Schwarz or the (v₀²+v₁²)/2 bound: once you have `map (·.1) μ₃ = map (·.2.1) μ₃ = gaussianReal 0 1`, both coordinates are L² and `MemLp.integrable_mul` finishes it.
18. `gaussianSmoothing φ x = ∫ u, inverseRegression φ (x+u) ∂γ` is the DEFINITION, so `∫ u, P (φ v + u) ∂γ = F (φ v)` is `rfl`. That single fact is what makes node R2b cheap and lets it be proved without the joint (V,Y) law (D3's A1b).

### Loss.lean — route
MUCH cheaper route than the one specified in the task, and it is worth propagating to the other Γ-consumers.

The task suggested "bound |F′(φ v)| ≤ ∫|u||P(φ v+u)| ∂γ; Tonelli + Cauchy–Schwarz with lemma22_memLp_two and E[U²]=1" for deliverable 1. None of that is needed. The Cauchy–Schwarz step is ALREADY banked as `integrable_noiseTraderLoss` (Statement.lean:897), which says the Γ integrand g(v,u) = u·P(φ v + u) is integrable on γ⊗γ. Then:

* deliverable 1 = `Integrable.integral_prod_left` applied to it (Mathlib: `Integrable f (μ.prod ν) → Integrable (fun x => ∫ y, f (x,y) ∂ν) μ`), because `deriv_gaussianSmoothing` + `deriv_gaussianSmoothing_eq_prob` (Regularity.lean) say F′(φ v) IS the inner slice `∫ u, u·P(φ v + u) ∂γ`;
* deliverable 2 = `MeasureTheory.integral_integral` on the same hypothesis.

So the paper's "conditioning on V, using independence" step (E[U·P(Y) ∣ V] = F′(φ(V)) a.s.) is literally Fubini's slice statement on γ⊗γ here: no condExp, no Tonelli, no lintegral work. Both are 2-line proofs. Total elaboration time for the whole module is ~1.5 s.

Deliverable 3: split the integrand and kill the cross term with `integral_prod_mul` + `integral_id_gaussianReal`; integrability of U·V from `Integrable.mul_prod` on `integrable_id_gaussianReal`. Product convention is Definitions.lean's: `(gaussianReal 0 1).prod (gaussianReal 0 1)` with p.1 = V, p.2 = U, so I also exposed the identical statement spelled with `stdModel.U / stdModel.V / stdModel.orderFlow` (`integral_noise_mul_sub_value_eq_noiseTraderLoss`) — it is `rfl`-equal, zero extra cost.

Deliverable 4: `equilibrium_iff_zeroSolution` (Statement.lean:694) does contain the identity, but only as an inner `have key : ∀ hφ P, IsPricingRule φ P → ∀ v x, expectedProfit P v x = objective 0 φ v x`, i.e. NOT exposed and not reachable. I re-proved only the canonical-version half of it (skipping `key`'s version-independence preamble, ~25 of its ~60 lines), as `expectedProfit_inverseRegression` (all v, x), then the requested form as a one-liner `.symm`. A closeout wave could now delete that half of `key` and call `expectedProfit_inverseRegression` instead, if/when Statement.lean becomes editable.

BONUS beyond the D5 brief, both cheap and both closing fidelity gaps:
* `covariance_noise_condExp_eq_noiseTraderLoss` — the Cov(U, E[V∣Y]) member of v4 Lemma 3.1's chain, against Mathlib's `ProbabilityTheory.covariance`. Definitions.lean's `noiseTraderLoss` docstring asserts "Γ := Cov(U, E[V ∣ Y]) (v3 eq. (13))" and nothing in the repo proved it; now it is machine-checked. Needed a 5-line private helper `covariance_congr_ae_right` (a.e.-congruence of `cov` in its second argument) — MISSING AT THE PIN, a candidate for upstreaming, and useful to the D3/Posterior agent if it wants the covariance form of P′.
* `noiseTraderLoss_id : noiseTraderLoss id = 1/2` — a sanity oracle for the whole route, consistent with `noiseTraderLoss_eq_half_iff` at a = 0. Analogue of D2's mandated `insiderProfit id = fun v => v^2/2` oracle.

`ProbabilityTheory.covariance` and the `cov[X, Y; μ]` notation are already transitively imported through `KyleUniqueness.Regularity`; NO new import was added. The file imports exactly `KyleUniqueness.Regularity` as instructed.

**Gotchas (pin-specific):**
1. `Integrable.comp_add_right` (used for the L¹ shift in `integrable_inverseRegression_const_add`) does NOT exist under that name in the source — grepping for it returns nothing. It is `to_additive`-generated from `MeasureTheory.Integrable.comp_mul_right` (Mathlib/MeasureTheory/Group/Integral.lean:139). Grepping the multiplicative name is the only way to verify it; the same trap will hit any agent grepping additive-group integral lemmas.

2. `integral_integral` needs `f` given EXPLICITLY (`integral_integral (f := fun v u => ...) h`). Higher-order unification of `Function.uncurry ?f` against a `fun p : ℝ × ℝ => ...` lambda will not solve on its own.

3. `MeasureTheory.Integrable.congr` and `integral_congr_ae` produce goals that are NOT beta-reduced: you get `(fun ω => …) ω = (fun ω => …) ω` and a bare `rw [hω]` fails with "did not find an occurrence". Use `simp only [hω]` (or the repo's `beta_reduce` idiom from Regularity.lean) instead. This cost me two of the four iterations.

4. `ProbabilityTheory.covariance` is a plain def — `rw [covariance]` fails; use `unfold ProbabilityTheory.covariance`. And there is NO `covariance_congr` / a.e.-congruence lemma at the pin; I wrote one privately (`covariance_congr_ae_right`). Note also that Covariance.lean is a `module`/`public import` file at this pin, so the notation `cov[X, Y; μ]` and `μ[X]` come along with `Mathlib.Probability.Notation` — both already reachable from `KyleUniqueness.Regularity`, no extra import needed.

5. `integral_const` on a probability measure leaves `(μ univ).toReal • c`; the simp lemma that clears it in this Mathlib is `probReal_univ` (NOT `measure_univ` / `ENNReal.one_toReal`). Pattern: `simp only [probReal_univ, one_smul]`.

6. `linter.unnecessarySimpa` fires as a *warning*, and a warning is a lint failure under this repo's `weak.linter.mathlibStandardSet`. It told me `simpa … using h` should be `simp`; naively editing to `simp … using h` is a PARSE error ("unexpected token 'using'"). Drop the `using` term entirely.

7. Deliverable-3's proof needs a trailing `rfl` after the `rw` chain: `∫ a, a.2 * inverseRegression φ (φ a.1 + a.2) ∂(γ.prod γ)` is defeq but not syntactically `noiseTraderLoss φ`, so `rw` cannot close it.

8. `KyleUniqueness/Posterior.lean` (the D3 agent's file) appeared in the tree mid-session — it did not exist when I first listed the directory. I did not read, import or touch it, and `lake build KyleUniqueness.Loss` does not pull it in. Anyone doing the umbrella/closeout wave should re-list the directory rather than trusting an earlier listing.

---

## Session 3 — 2026-09-16, Wave 2: E2 and H1 (both hard blocks) + J1 CLOSED

**Result:** `Accounting.lean` (826 LOC; v4 Prop 5.1 by the full v4 route — L² transport of the four products through the μ₃ marginals, (5.1), clamp truncation (5.2), two monotone-convergence passes; main theorem `accounting_identity`, consumers `integrable_insiderProfit_of_isGammaSolution`, `noiseTraderLoss_eq_integral_insiderProfit`) and `SignedRoot.lean` (530 LOC; `criticalPoint`, `posteriorSlope`, `signedRoot`, `rootSlope`, a.e. derivative, moment dictionary, `noiseTraderLoss_pos`, and J1 `one_le_two_mul_noiseTraderLoss` via the banked Stein inequality per decision D7; sanity oracles at φ = id incl. `one_le_two_mul_noiseTraderLoss_id`). **0 sorries**, all public declarations axiom-clean, lint-clean; both verified adversarially on the first round. Hard-block census: 0 of 5 remain.

Known coordination item: `integral_insiderProfit_id` (and possibly the φ = id oracle helpers) are declared in BOTH new modules; to be deduplicated when Main.lean imports both.

### Accounting.lean — route
FULL v4 ROUTE, NO FALLBACK. All 9 deliverables landed; the v3 aₙ/FOC fallback was not needed.

PART I (transport, then four products).
The single highest-leverage move is identifying the common 2-D marginal of μ₃ with the law of (V,Y) on stdModel: `Resampling.resamplingMeasure_map_fst`/`_map_snd` give the (V⁰,Y)- and (V¹,Y)-marginals in DENSITY form `ϱ(v)ϱ(y−φ v)`, and `Posterior.map_value_orderFlow` says that same withDensity is `map (fun w => (w.1, φ w.1 + w.2)) (γ⊗γ)`. The two withDensity spellings are defeq (`jointDensity` is a plain def), so `rw [resamplingMeasure_map_fst hφ, map_value_orderFlow hφ]; rfl` closes the bridge in two lines. Everything about U⁰ and U¹ then becomes a statement about the SECOND COORDINATE of γ⊗γ, because (φ w.1 + w.2) − φ w.1 = w.2. That yields, via `integral_map` / `memLp_map_measure_iff` twice (private `integral_pair_v0/v1`, `memLp_pair_v0/v1`):
 * MemLp 2 of U⁰ and U¹ (paper's "(V⁽¹⁾,U⁽¹⁾) =ᵈ (V⁽⁰⁾,U⁽⁰⁾)"), plus MemLp 2 of P(Y) straight from `lemma22_memLp_two` (no re-proof);
 * E[U⁰V⁰] = 0 as a 4-line independence computation (`integral_prod_mul` + `integral_id_gaussianReal`), NOT a density computation;
 * E[U⁰P(Y)] = Γ literally by `rfl` after one `mul_comm` (Γ's definiens IS ∫ w.2 · P(φ w.1 + w.2) on γ⊗γ).
V⁰,V¹ ∈ L² are re-proved locally (Resampling's `memLp_two_v0/v1` are private) in 5 lines each from `resamplingMeasure_map_v0/v1`.
Exchangeability is packaged once as `integral_resampling_swap hφ hf : ∫ q, f (q.2.1,q.1,q.2.2) ∂μ₃ = ∫ q, f q ∂μ₃` (integral_map + `resamplingMeasure_map_swap`); E[U¹V¹]=0 and E[U¹V⁰]=E[U⁰V¹] are then one `exact` each with the right choice of f.

DELIVERABLE 3 (the L² clause (iii)) — the one place the task predicted trouble, solved WITHOUT redoing Tonelli on the flat density. Instead of integrating v₁ out of ϱ(v₀)ϱ(y−φv₀)ϱ(v₁)ϱ(y−φv₁)/p(y) by hand, I truncate the TEST FUNCTION: `integral_v1_mul_eq_inverseRegression hφ (clampAt n ∘ g)` is legal for every n (clampAt n is bounded by n), and two applications of `tendsto_integral_of_dominated_convergence` with the Cauchy–Schwarz majorants |V¹·g| and |P(Y)·g| (both integrable because V¹, P(Y), g(V⁰,Y) ∈ L²(μ₃)) push n → ∞ on both sides; `tendsto_nhds_unique` finishes. ~55 lines, no access to Resampling's private `rd`/`jd`/`integral_rd_v1_id` needed. The resulting lemma is stated for a general Borel g with g(V⁰,Y) ∈ L²(μ₃), which is strictly more general than the y − φ(v₀) instance v4 §5 uses.

PART II (5.2). Stated as `(1/2)·∫(φₙ(v₀)−φₙ(v₁))(v₀−v₁) dμ₃ = ∫ φₙ(v)(v−F(φ v)) dγ`. Proof: exchangeability applied to f q := φₙ(φ q.1)·(q.2.1 − q.1) shows the two halves of the increment have OPPOSITE integrals, so ∫(A−B) = 2∫A with A = φₙ(v₀)(v₀−v₁) — that is exactly the paper's first displayed equality in (5.2). Then ∫φₙ(v₀)v₀ dμ₃ = ∫φₙ(v)v dγ by the 1-D v₀-marginal (`resamplingMeasure_map_v0`), and ∫φₙ(v₀)v₁ dμ₃ = ∫F(φv)φₙ(v) dγ is `integral_v1_mul_comp_eq_gaussianSmoothing` with k := clampAt n, C := n (Resampling's clause (iv) is already in exactly the right shape — no upgrade needed there, since φₙ IS bounded). Integrability throughout is `Integrable.bdd_mul` against `integrable_v0/v1_resampling`, `integrable_id_gaussianReal`, `integrable_gaussianSmoothing_comp`.

PART III (5.3) — ONE DELIBERATE DEPARTURE FROM THE PAPER, recorded in the module docstring. v4 argues by monotone convergence (|φₙ(V⁰)−φₙ(V¹)| ↑ |φ(V⁰)−φ(V¹)| as the length of [−n,n] ∩ [φ(V⁰),φ(V¹)]). Since (5.1) already exhibits the LIMIT as integrable (it is the combination of the four Cauchy–Schwarz products), I use DOMINATED convergence with that limit as the majorant instead. This is strictly cheaper and avoids ever proving that n ↦ clampAt n a − clampAt n b is monotone (which is a genuinely fiddly 4-case interval-length argument); all that survives is the one-sided Lipschitz bound `clampAt_sub_le`, proved by `simp only [clampAt, max_def, min_def]; split_ifs <;> linarith`. Mathematically this is a strengthening of the paper's step, not a weakening: MCT there only ever concludes what DCT concludes here.

PART IV — the paper's three-case argument verbatim, isolated as the pure-real private lemma `clamp_mul_facts {s t : ℝ} (h : 0 ≤ s*t)` (s := φ v, t := v − F(φ v)): s < 0 ⇒ t ≤ 0, clampAt n s = max(−n,s) ≤ 0 is ANTITONE in n, and multiplying by t ≤ 0 reverses; s = 0 ⇒ everything is 0; s > 0 ⇒ t ≥ 0 and clampAt n s = min(s,n) ≥ 0 is monotone. The Tendsto clause needs no case split at all (`(tendsto_clampAt (φ v)).mul_const _`). The extended expectation E[Π(V)] ∈ [0,∞] is realised as ∫⁻ ofReal (Π v) ∂γ; MCT is `lintegral_tendsto_of_tendsto_of_monotone`, each ∫⁻ ofReal (gₙ) is rewritten to ofReal (∫ gₙ) by `ofReal_integral_eq_lintegral_ofReal`, and `tendsto_nhds_unique` against `ENNReal.tendsto_ofReal hΓ` gives ∫⁻ ofReal Π = ofReal Γ. Integrability is then `lintegral_ofReal_ne_top_iff_integrable` (NOTE: there is no `integral_tendsto_of_tendsto_of_monotone` at this pin — the Bochner MCT that takes Integrable F as a HYPOTHESIS would have been useless here anyway, since integrability of Π is what we are proving), and the value is `integral_eq_lintegral_of_nonneg_ae` + `ENNReal.toReal_ofReal` with Γ ≥ 0 from `ge_of_tendsto'`.

CONSUMER INTERFACE FOR THE NEXT WAVES
 * `noiseTraderLoss_eq_integral_insiderProfit (h : IsGammaSolution 0 φ) : noiseTraderLoss φ = ∫ v, insiderProfit φ v ∂γ` and `integrable_insiderProfit_of_isGammaSolution` are the two E2 exports J1/T3/H1 should consume. Both hypotheses of Prop 5.1 come free from ValueFunction: `monotone_of_isGammaSolution` and `insiderProfit_nonneg` (the latter gives ∀ v, so `ae_of_all`).
 * `accounting_identity` itself is hypothesis-minimal: it does NOT need IsGammaSolution, only Measurable + Monotone + a.e. nonnegativity of Π. If a later node has monotonicity from somewhere else, it can use the general form.
 * `integral_resampling_swap`, `integral_pair_v0`, `integral_pair_v1` are reusable μ₃ ↔ γ⊗γ plumbing for any further Lemma-2.6 consumer.
 * `integral_v1_mul_eq_inverseRegression_memLp` is the L² version of clause (iii); if a later node needs the L² version of clause (iv) the same truncation+DCT recipe applies verbatim.

VERIFICATION PERFORMED
 * `lake build KyleUniqueness.Accounting` green from a DELETED olean (15 s, "Build completed successfully (3128 jobs)"); this is the run that applies the package's `weak.linter.mathlibStandardSet`. Zero warnings attributable to this file — the only build output is the pre-existing noise (2 `sorry` warnings from Statement.lean:1283/1339 and the `ring`→`ring_nf` info at Regularity.lean:57), exactly as PROVING_LOG gotcha #14 predicts.
 * `#print axioms` on all 38 public declarations, run OUT OF TREE from a scratch file importing KyleUniqueness.Accounting: every one is `[propext, Classical.choice, Quot.sound]`.
 * 0 occurrences of the string `sorry` in the file.
 * NON-VACUITY, out of tree: `IsGammaSolution 0 (id : ℝ → ℝ)` is provable in 4 lines (objective 0 id v x = x(v − x/2), and x(v−x/2) ≤ v²/2 is (v−x)² ≥ 0 by nlinarith), so both `IsGammaSolution`-fronted corollaries are non-vacuous; both were applied to it successfully.
 * SANITY ORACLE, in the file: `integral_insiderProfit_id : ∫ v, insiderProfit id v ∂γ = 1/2`, obtained by feeding φ = id to `accounting_identity` and closing with `noiseTraderLoss_id`. Out of tree this was then unwound to the independent classical fact `∫ v, v²/2 ∂(gaussianReal 0 1) = 1/2`, i.e. E[V²] = 1 — a genuine numerical cross-check of the whole chain (Γ-side and Π-side computed by completely different routes and agreeing). It also certifies that all three hypotheses of the main theorem are simultaneously satisfiable.
 * Max line length 91 characters (an `awk length` scan reports two >99 lines, but that is a byte-count artifact of the ⁽¹⁾ superscripts in docstrings; a UTF-8-aware count gives 91).
 * Dead-code scan: all 11 private lemmas are used; no unused privates.
 * `git status --porcelain` shows only `?? KyleUniqueness/Accounting.lean` from this session (the other untracked file, `KyleUniqueness/SignedRoot.lean`, is a parallel agent's; it was never read, imported or touched, per the instruction).

NOT DONE (per rule 1): the module is NOT added to `KyleUniqueness.lean` or `AxiomAudit.lean`. The closeout wave must add `import KyleUniqueness.Accounting` to both and the 38 `#print axioms` lines to AxiomAudit; until then it only builds via the explicit target `lake build KyleUniqueness.Accounting`.

**Gotchas (pin-specific):**
Pin-specific facts worth banking in PROVING_LOG.md:

1. **`Π` (U+03A0) is NOT a legal Lean 4 identifier character** — same exclusion as `λ`. `(hΠ : ...)` fails with `unexpected token 'Π'; expected ':=' or '|'`, and so does any name containing it (`hmΠ`, `foo_Π`). Use `hPi`. Blueprint/task text that writes `hΠ` must be transliterated. (`Γ`, `φ`, `μ`, `γ`, `σ`, `τ` are all fine; only Π, Σ and λ are excluded from the Greek block.)

2. **`push_neg` is DEPRECATED at this pin** and emits a warning ("Prefer using `push Not`"), which counts as a lint failure under this repo's `weak.linter.mathlibStandardSet` build. `by_contra hc; rw [not_le] at hc` is the warning-free replacement for the common `¬ (a ≤ b)` case.

3. **There is NO `integral_tendsto_of_tendsto_of_monotone` (Bochner MCT) at this pin.** Only the `ℝ≥0∞` version `lintegral_tendsto_of_tendsto_of_monotone` (Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:113) exists. For "prove f is integrable AS the conclusion of MCT", the working recipe is: ∫⁻ ofReal (fₙ) ↑ ∫⁻ ofReal (f) by that lemma; rewrite each ∫⁻ ofReal (fₙ) as ofReal (∫ fₙ) by `ofReal_integral_eq_lintegral_ofReal`; identify the limit with `tendsto_nhds_unique` against `ENNReal.tendsto_ofReal`; conclude integrability from `lintegral_ofReal_ne_top_iff_integrable` (a `section ENNReal`, i.e. root-`MeasureTheory` name, not `ENNReal.`-prefixed) and the value from `integral_eq_lintegral_of_nonneg_ae` + `ENNReal.toReal_ofReal`.

4. **`min_le_min` exists only as a `to_dual`-generated name** of `max_le_max` (Mathlib/Order/MinMax.lean:54). Grepping `theorem min_le_min` returns NOTHING; grep `max_le_max` (or just use it — it resolves). Same trap family as Loss.lean's `Integrable.comp_add_right`/`comp_mul_right` note.

5. **Nested `max`/`min` inequalities: `simp only [max_def, min_def]; split_ifs <;> linarith` is a reliable brute force.** `clampAt_sub_le` (the 1-Lipschitz bound for `max (-n) (min t n)`) went through first try this way, where a hand case-split would have been ~20 lines.

6. **`calc` is the antidote to the beta-redex problem when consuming a lemma stated as `∫ q, f (q.1, q.2.2) ∂μ`** with `f` a variable. Instantiating `f` with a lambda produces `(fun r => …) (q.1, q.2.2)`, which `rw` cannot match against the goal. Every `calc` step is checked by `exact`-style defeq, so writing the whole computation as one `calc` chain makes the redexes invisible. This is the cheap alternative to the `dsimp only` / `beta_reduce` idiom the earlier waves used, and it is what made the four Part-I identities 5 lines each.

7. **The trick for forcing an explicit-lambda `Integrable`/`MemLp` out of Pi-level combinators** (`.add`, `.sub`, `MemLp.integrable_mul`, which all produce `f + g`, `f - g`, `f * g` at Pi level) is a type-ascribed `have`: `have h : Integrable (fun q => <explicit lambda>) μ := hA.sub hB`. The ascription is checked by defeq and the resulting hypothesis is then usable by `rw`/`integral_sub`. This generalises PROVING_LOG Posterior gotcha #1 to a one-line recipe.

8. **`resamplingMeasure_map_fst`/`_map_snd` (Resampling, density form) and `map_value_orderFlow` (Posterior, `withDensity (jointDensity φ)`) are the SAME measure, and the bridge is `rw [resamplingMeasure_map_fst hφ, map_value_orderFlow hφ]; rfl`** — the trailing `rfl` is needed because `jointDensity` is a plain `def` and `rw` does not close the delta step on its own. Decision D4 told Resampling not to import Posterior; a downstream file that imports both gets the identification for free, and it is worth much more than it costs: it converts every (V⁽ⁱ⁾,Y) statement on μ₃ into a statement about the second coordinate of γ⊗γ.

9. **Upgrading a bounded-test-function clause to L² test functions costs ~55 lines by truncation + DCT and needs NO access to the provider file's private density machinery.** Recipe: truncate the test function with `clampAt n`, apply the bounded clause at each n, and run `tendsto_integral_of_dominated_convergence` on each side with the Cauchy–Schwarz majorant `|X · g|`; the pointwise limit is free because `clampAt n t = t` eventually (`tendsto_atTop_of_eventually_const (i₀ := ⌈|t|⌉₊)`). Recommend this over re-deriving Tonelli whenever a Wave-1 module exports only the bounded form.

10. **`Filter.Tendsto.const_mul` takes the constant as its FIRST EXPLICIT argument** and concludes about `(b * f ·)`; dot notation `(h).const_mul c` still routes `h` to the `Tendsto` slot, so `(tendsto_clampAt x).const_mul c` is correct. `Filter.Tendsto.congr (hl : ∀ x, f₁ x = f₂ x) (h : Tendsto f₁ …)` likewise takes the function equality FIRST, so `h.congr hl` is the usable spelling.

11. **`lake env lean` remains ~3 s warm on a 826-line file with these imports but STILL does not run the style linters** (confirmed again: a file that was silent under `lake env lean` for the whole session produced zero new warnings under `lake build` only because I had already wrapped to 99 columns and avoided `show`). Budget the `lake build` pass; and note that `awk 'length>99'` over a Lean file with superscripts (⁽¹⁾, ᵈ, ᵐ) over-reports because `awk` counts bytes — verify with a UTF-8-aware counter before rewrapping.

12. `memLp_id_gaussianReal` takes its exponent as `ℝ≥0`, not `ℝ≥0∞`; the working incantation (copied from Statement.lean) is `simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2`.

### SignedRoot.lean — route
ROUTE ACTUALLY TAKEN (all deliverables 1-10 landed; 50 public declarations, 0 private helpers, 0 sorries).

D1 (c and signs). `strategy_criticalPoint`: maximisation at v = c against the admissible order x = 0 gives 0 ≤ φ(c)(c − F(φ(c))); `strictMono_gaussianSmoothing_of_strictMono` then kills both signs of φ(c) ≠ 0 by nlinarith. No uniqueness-of-argmax lemma is needed — the contradiction form is cheaper than the paper's "0 is the unique maximiser" phrasing. The four sign clauses (strict and non-strict, both sides) are one-line rewrites of StrictMono/Monotone φ through φ(c) = 0.

D2 (q). posteriorSlope is literally deriv (gaussianSmoothing φ) ∘ φ, so integrable_posteriorSlope and noiseTraderLoss_eq_integral_posteriorSlope are RE-EXPORTS of Loss.lean's integrable_deriv_gaussianSmoothing_comp / noiseTraderLoss_eq_integral_deriv (definitional, zero proof). noiseTraderLoss_pos = integral_pos_iff_support_of_nonneg_ae + Function.support q = univ + measure_univ; 4 lines.

D6 (monotonicity of W on each side of c) — THE DESIGN CHOICE THAT SAVED THE MOST WORK. I did NOT use insiderProfit_sub_eq_intervalIntegral (which would have needed a strict-positivity argument for an interval integral of a monotone function). Instead: pick m strictly between v and w by `exists_between`, apply the subgradient inequality (A.1) TWICE (v→m and m→w), and note that φ(m) has a strict sign because m is strictly off c. Both `insiderProfit_lt_of_criticalPoint_le` and `insiderProfit_lt_of_le_criticalPoint` are 7 lines of nlinarith. This is the whole content of the paper's "W = φ²q > 0 on J" plus its monotonicity claim, without any compactness.

D6 (continuity). The paper's local-Lipschitz-at-c argument is replaced by `Continuous.if_le`: rewrite the definition from `if v < c then −g v else g v` to `if c ≤ v then g v else −g v` (so f := const c, g := id), and the gluing hypothesis `∀ x, c = x → g x = −g x` is discharged at x = c by W(c) = 0. 6 lines total. NOTE: continuity of h is NOT needed by the Stein inequality — it is exported as a bonus/faithfulness item only.

D7 (a.e. derivative). At v ≠ c with φ continuous at v: `(hasDerivAt_insiderProfit_of_continuousAt h hcont).const_mul 2 |>.sqrt hne` gives derivative 2φ(v)/(2√(2W v)); the new lemma `sqrt_two_mul_insiderProfit` (√(2W) = |φ|·√(2q), from eq. (2.5) under Real.sqrt_mul + Real.sqrt_sq_eq_abs) converts it to (√(2q v))⁻¹ = rootSlope φ v after abs_of_neg / abs_of_pos. Locality is `HasDerivAt.congr_of_eventuallyEq` against `Iio_mem_nhds` / `Ioi_mem_nhds`. The exceptional set is handled exactly as ValueFunction.lean's ae_hasDerivAt_insiderProfit: two `Set.Countable.ae_notMem volume` filter_upwards, one for `Monotone.countable_not_continuousAt`, one for `Set.countable_singleton (criticalPoint φ)`.

D8 (moments). Pure algebra as specified: the two pointwise dictionary identities turn each integrand into `2 * (something already known integrable)`, so `integrable_const_mul_iff (isUnit_iff_ne_zero.2 two_ne_zero)` gives the iff, `Integrable.const_mul` the one-directional fact, and `integral_congr_ae` + `integral_const_mul` the two integral identities. No new integrability work at all.

D9 (J1). One application of `one_le_sqrt_integral_sq_mul_integral_inv_sq` (SteinInequality.lean:858) with f := signedRoot φ, f' := rootSlope φ; then `rw [integral_sq_signedRoot, integral_inv_sq_rootSlope, ← hΓ, Real.sqrt_mul_self (by linarith [noiseTraderLoss_pos h])]`. The whole proof is 8 lines. Note the sqrt collapse is `Real.sqrt_mul_self`, not sq_sqrt: `2Γ * (2Γ)` is already syntactically `a * a`.

D10 (oracles). `isGammaSolution_zero_id` is re-derived locally from `gaussianSmoothing_id` + `nlinarith [sq_nonneg (v − x)]` (4 lines) so that NOTHING in this file touches Statement.lean's still-sorried `isGammaSolution_zero_iff`. All five oracle values check out (c = 0, q ≡ 1/2, h = id, r ≡ 1, 2Γ = 1), and `one_le_two_mul_noiseTraderLoss_id` instantiates J1 with BOTH Proposition-5.1 hypotheses discharged (via `integrable_sq_gaussianReal_std` from Posterior.lean and `integral_mul_self_gaussianReal_std` from GaussianHelpers.lean), proving the bound is attained and therefore that no hypothesised theorem here is vacuous.

DOWNSTREAM NOTE FOR T3 (verified out-of-tree, compiles): node T3 is now two lines. `have hup := (abs_le.1 (noiseTraderLoss_le_half h.1)).2; have hlo := one_le_two_mul_noiseTraderLoss h hint hΓ; linarith` proves `noiseTraderLoss φ = 1/2` (v4 Proposition 6.1 in full). The only missing inputs are Accounting's two Prop-5.1 outputs.

VERIFICATION PERFORMED
* `lake build KyleUniqueness.SignedRoot` green TWICE, the second time from a deleted olean/ilean/trace ("Built KyleUniqueness.SignedRoot (2.3s)", "Build completed successfully (3128 jobs)"). This is the lint-bearing command.
* Explicit lint pass `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true KyleUniqueness/SignedRoot.lean` prints NOTHING. All lines ≤ 99 chars.
* `#print axioms` out-of-tree on all 50 public declarations (scratch file importing only the built module): 50/50 = `[propext, Classical.choice, Quot.sound]`. No sorryAx despite Statement.lean's two pre-existing sorries being in the transitive import closure.
* 11 independent cross-checks in a scratch file, all compiling: (a) both sides of `integral_sq_signedRoot` at φ = id evaluate to 1 by two INDEPENDENT routes (through the theorem, and directly from `signedRoot_id` + the Gaussian second moment); (b) same for `integral_inv_sq_rootSlope`; (c) sign convention h < 0 below c and h > 0 above c; (d) `ae_hasDerivAt_signedRoot` at φ = id reduces to `HasDerivAt id 1` a.e.; (e) J1 tight at φ = id; (f) the T3 assembly above.
* Only my new file was created; git status shows exactly `?? KyleUniqueness/SignedRoot.lean` (plus the parallel wave's `?? KyleUniqueness/Accounting.lean`, untouched). Nothing committed. `KyleUniqueness.lean` and `AxiomAudit.lean` are untouched per rule D9 — the closeout wave must add `import KyleUniqueness.SignedRoot` to both and the 50 `#print axioms` lines to AxiomAudit; until then the module is a leaf reachable only via `lake build KyleUniqueness.SignedRoot`.

**Gotchas (pin-specific):**
Pin-specific facts worth banking in PROVING_LOG.md (I could not append them myself — rule 1 forbids editing other files).

1. **`lt_or_le` DOES NOT EXIST at this pin.** It is `lt_or_ge (a b : α) : a < b ∨ b ≤ a` (Mathlib/Order/Defs/LinearOrder.lean:97), with `le_or_gt` as the companion. `rcases lt_or_le x y with h | h` fails with "Unknown identifier `lt_or_le`" followed by a confusing second error ("`x✝ : ?m` is not an inductive datatype"). This cost two iterations because the second error masks the first.

2. **`HasDerivAt.neg` produces a Pi-level `-f`**, the same family as Wave-1's `Integrable.sub` gotcha. `hsq.neg.congr_of_eventuallyEq` leaves the goal `-√(2 * W u) = (-fun u => √(2 * W u)) u`, which `rw` cannot close. FIX: bind the negated derivative to an explicit-lambda `have` first — `have hneg : HasDerivAt (fun u => -Real.sqrt (2 * insiderProfit φ u)) (-(...)) v := hsq.neg` — and use `hneg`. The ascription forces the lambda form by defeq.

3. **`field_simp` needs the `≠ 0` side conditions passed as EXPLICIT simp arguments**; having `0 < s` or `φ v < 0` in the local context is not enough. `field_simp` alone left the residual goal `φ v / φ v = 1`. Use `field_simp [hφv.ne, hspos]` with `hspos : Real.sqrt (...) ≠ 0` stated as a `≠ 0` (not as `0 < ...`).

4. **`Real.sqrt` lemmas live in `Mathlib/Analysis/Real/Sqrt.lean`, NOT under `Mathlib/Analysis/SpecialFunctions/`.** Grepping the SpecialFunctions tree for `sq_sqrt` returns nothing. Worse, the same file opens with an `NNReal` section whose `sq_sqrt`, `sqrt_sq`, `sqrt_pos`, `sqrt_mul`, `sqrt_one` shadow the real-valued ones — always grep the whole of Mathlib and check which section a hit is in. The real-valued forms are `Real.sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x` (line 178), `Real.sqrt_sq_eq_abs` (189), `Real.sqrt_mul (hx : 0 ≤ x) (y)` (366), `Real.sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y)` (221), `Real.sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x` (149), `Real.sqrt_pos` (286), `Real.continuous_sqrt` (126), `Continuous.sqrt` (476). The derivative is `HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x` in `Mathlib/Analysis/SpecialFunctions/Sqrt.lean:84` — note the `f' / (2 * √(f x))` shape, not `f' / (2 √)` pre-simplified.

5. **`Continuous.if_le` (Mathlib/Topology/Order/OrderClosed.lean:677) is the right glue for any `sign(v − c)·g(v)` construction**, but only for `≤`. Signature: `(hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x = g x → f' x = g' x) : Continuous fun x => if f x ≤ g x then f' x else g' x`. So first rewrite `if v < c then A else B` into `if c ≤ v then B else A` (f := const c, g := id) by a `funext` + `by_cases` + `if_pos`/`if_neg`; then `continuous_const` and `continuous_id` fill the last two slots and the elaborator accepts `id x` against `x` without complaint.

6. **`sq_pos_of_ne_zero` is the live name** (`pow_two_pos_of_ne_zero` is a deprecated alias; `sq_pos_iff : 0 < a ^ 2 ↔ a ≠ 0` at Mathlib/Algebra/Order/Ring/Basic.lean:209). `positivity` cannot prove `0 < φ v ^ 2` from a hypothesis `φ v ≠ 0`. Relatedly, `positivity` DID close `2 * insiderProfit φ v ≠ 0` for me with `hWpos` in context, but I replaced it with the explicit `ne_of_gt (by linarith)` because that behaviour is not something to rely on.

7. **`integral_pos_iff_support_of_nonneg_ae (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) : 0 < ∫ x, f x ∂μ ↔ 0 < μ (Function.support f)`** (Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:747) is the 4-line route to strict positivity of an integral against a probability measure: rewrite with it, prove `Function.support f = Set.univ` by `ext v; simp [Function.mem_support, (hpos v).ne']`, then `rw [hsupp, measure_univ]; exact zero_lt_one`. Note the goal after the last rewrite is in `ℝ≥0∞`.

8. **`integrable_const_mul_iff (hc : IsUnit c) (f)` (Integrable.lean:1056)** is the iff form for `Integrable (fun x => c * f x) μ ↔ Integrable f μ`; feed it `isUnit_iff_ne_zero.2 two_ne_zero`. This is much cleaner than proving both directions with `.const_mul` and a congr.

9. **`Measurable.ite measurableSet_Iio h1.neg h1`** handles `Measurable fun v => if v < c then -g v else g v` directly — `{a | a < c}` is defeq to `Iio c`, so `measurableSet_Iio` is accepted with no `Set.ext` step. (Signature: `Measurable.ite {p} {_ : DecidablePred p} (hp : MeasurableSet {a | p a}) (hf) (hg)`.)

10. **`Integrable.const_mul (h) (c) : Integrable (fun x => c * f x) μ`** takes `c` as an EXPLICIT trailing argument (`h.const_mul 2`), unlike most `const_*` lemmas; `Integrable.const_mul'` is the Pi-level variant and will not match an explicit-lambda goal.

11. Reconfirming the Wave-1 note: `lake env lean <file>` still does not run `weak.linter.mathlibStandardSet`. Both of my lint-clean claims come from `lake build KyleUniqueness.SignedRoot` and from an explicit `-Dweak.linter.mathlibStandardSet=true` invocation. Pre-existing noise to ignore when checking a new module: two `declaration uses sorry` warnings from `Statement.lean:1283,1339` and one `ring → ring_nf` info from `Regularity.lean:57`.

12. The `shell` in this harness has no `timeout` binary (BSD userland); use the tool's own `timeout` parameter for long Lean runs.

---

## Session 3 — 2026-09-16, Wave 3: T3, N2, O1 CLOSED — **0 sorries, headline axiom-clean**

**Result:** `Main.lean` (new top module) now carries the six headline declarations moved out of `Statement.lean` (the import DAG forced the move: Statement sits below every Session-3 module). Proved there: `gamma_eq_half` (v4 Prop 6.1 on the normalised model = J1 + Prop 4.1), the helper `Monotone.eq_of_ae_eq_continuous`, `isGammaSolution_zero_iff` (v4 Theorem 7.1, both directions), `existsUnique_zeroSolution`, and — via the v4 §7 standardisation `stdStrategy`/`stdPricingRule` — `isEquilibrium_eq_kyleStrategy` (v4 Theorem 1.1, strategy half) with its consumers `kyle_unique_equilibrium`, `kyle_existsUnique_equilibrium`, `kyle_equilibrium_pair_iff`. Root module imports everything; `AxiomAudit.lean` audits all Session-3 declarations. **From-scratch `lake build`: green, 3149 jobs, 0 `declaration uses sorry`, 0 `sorryAx`**; the six headline theorems depend on `[propext, Classical.choice, Quot.sound]` only. Total 9,612 Lean LOC. Both stages and the final audit passed adversarial verification on the first round.

### Stage A (rigidity) — route
STAGE A — all five deliverables landed. Full from-scratch rebuild: `Build completed successfully (3149 jobs)`, exit 0.

A0 — DUPLICATE NAMES. Exhaustive scan (`grep -hoE '^(theorem|lemma|def|noncomputable def|abbrev|…) +NAME' KyleUniqueness/*.lean | sort | uniq -d`) found EXACTLY ONE duplicate across the whole tree: `integral_insiderProfit_id` (Accounting.lean:820, SignedRoot.lean:510). The other suspects named in the brief are NOT duplicated — `isGammaSolution_zero_id` and `integrable_insiderProfit_id` exist only in SignedRoot.lean. Resolved by renaming SignedRoot's to `integral_insiderProfit_id'` (2 occurrences: the declaration and its use in `one_le_two_mul_noiseTraderLoss_id`), with a docstring note explaining that Accounting proves the same identity by the other route. `lake build KyleUniqueness.SignedRoot` green afterwards. Rationale for choosing the prime over the import-and-delete option is in `blockers`.

A1/A2 — MOVE. Created `KyleUniqueness/Main.lean` (250 LOC) importing `KyleUniqueness.Accounting` and `KyleUniqueness.SignedRoot` — that closure already contains Statement (Accounting → ValueFunction → Regularity → Statement), Posterior/PosteriorDeriv, Resampling, Loss and SteinInequality, so no further imports were needed. All six declarations moved with names, statements and docstrings verbatim; only the two `SCHEDULED` comments were rewritten (`isGammaSolution_zero_iff`'s now reads "blueprint N2, CLOSED" and records the actual route; `isEquilibrium_eq_kyleStrategy`'s now says Theorem 4 is PROVED and that O1's location–scale standardisation is the only thing left). Statement.lean's module docstring gained a "## Moved to `KyleUniqueness.Main`" section listing all six, its "Every `sorry` in this file is an open proof obligation" sentence became "This file is `sorry`-free", and a `kyleStrategy_isEquilibrium` / `kyleStrategy_kylePricingRule_isEquilibrium` bullet replaced the moved entries in "Main statements". Nothing else was deleted: `kyleStrategy_isEquilibrium`, `isPricingRule_kylePricingRule`, `pricingRule_ae_eq_kylePricingRule`, `eq_kylePricingRule_of_continuous`, `kyleStrategy_kylePricingRule_isEquilibrium`, `pricingRule_ae_orderFlow` and `expectedProfit_congr_ae` all still build in Statement.lean (1408 LOC, 0 sorries).

A3 — PROOFS. All three landed exactly on the prescribed routes.

* `gamma_eq_half` (v4 Prop 6.1, node T3) — 6 lines, verbatim the route the SignedRoot wave predicted: `one_le_two_mul_noiseTraderLoss h (integrable_insiderProfit_of_isGammaSolution h) (noiseTraderLoss_eq_integral_insiderProfit h)` for `1 ≤ 2Γ`, `(abs_le.1 (noiseTraderLoss_le_half h.1)).2` for `Γ ≤ 1/2`, `linarith`. Stated under `IsGammaSolution 0 φ` rather than the paper's "(φ,P) is an equilibrium", which is what v4's own proof of Prop 6.1 reduces to in its first three lines and what Theorem 7.1 then consumes; `equilibrium_iff_zeroSolution` already bridges the two.

* `Monotone.eq_of_ae_eq_continuous` — the density squeeze, ~30 lines, no Metric/ε-δ and no `Dense` API. Structure: (i) `ae_iff.1 hae` gives the null disagreement set; (ii) `hmeet : ∀ a b, a < b → ∃ x ∈ Ioo a b, φ x = g x` by `by_contra` + `measure_mono_null` + `Real.volume_Ioo` + `ENNReal.ofReal_eq_zero` + `linarith`; (iii) `funext v; refine le_antisymm ?_ ?_`, each half by `by_contra` + `not_le`, `isOpen_Iio.mem_nhds` / `isOpen_Ioi.mem_nhds` fed to `ContinuousAt.preimage_mem_nhds`, then `mem_nhds_iff_exists_Ioo_subset` to get `Ioo l u`, then `hmeet` on the correct side of `v` and one `Monotone` application. This is precisely the sentence v4 Theorem 7.1 discharges in one line ("Because φ is increasing and agrees almost everywhere with the continuous function v ↦ v+a, this equality holds for every v ∈ ℝ").

* `isGammaSolution_zero_iff` (⇒) — the prescribed chain: `gamma_eq_half h` → `(noiseTraderLoss_eq_half_iff h.1).1` → `⟨a, ha⟩` → the helper against `monotone_of_isGammaSolution h` and `Continuous (· + a)` (`by fun_prop`) → `φ = fun v => v + a` everywhere. For the argmax step I took the comparison at **v = 0, x = a/2** rather than general `v`: `rw [hφa] at hcmp; simp only [objective, gaussianSmoothing_affine] at hcmp` reduces `h.2 0 (a/2)` to `a²/8 ≤ 0` (LHS `(a/2)(0 − (a/2−a)/2) = a²/8`, RHS `a(0 − (a−a)/2) = 0`), so `nlinarith` gives `a ^ 2 ≤ 0` and `sq_eq_zero_iff.1 (le_antisymm hsq (sq_nonneg a))` gives `a = 0`. Same content as the paper's "the unique maximiser is v + a/2, so v + a = v + a/2", one specialisation cheaper. (⇐) is the existing proof verbatim. The remaining five moved theorems are byte-identical to their Statement.lean originals.

A4 — WIRING. `KyleUniqueness.lean` now imports all 18 modules with AxiomAudit last. `AxiomAudit.lean` imports `KyleUniqueness.Main` plus `BeyondPaper` and `IdentityTheoremSpike` — note Main's closure does NOT reach those two leaves, so importing Main alone would have silently dropped `cubic_*`, `betaGamma_*`, `lambdaGamma*` and `analyticOnNhd_*` from the audit. Every pre-existing `#print axioms` line kept and still resolving; 122 new lines added covering the six Session-3 modules (ValueFunction: all 24 public declarations; Posterior: 26; Resampling: all 20; Loss: all 11; Accounting: 16; SignedRoot: 26) plus `gamma_eq_half` and the fully-qualified `KyleUniqueness.Monotone.eq_of_ae_eq_continuous`. Every name in the brief's "at least" list is present and resolved. Header prose rewritten to the Session-3 state: one open carrier, three inheriting consumers, everything else clean.

A5 — GATE. Deleted `.lake/build/lib/lean/KyleUniqueness*` entirely and reran bare `lake build`: exit 0; ONE `warning: KyleUniqueness/Main.lean:189:8: declaration uses 'sorry'`; 221 `depends on axioms` lines of which exactly 4 carry `sorryAx` (`isEquilibrium_eq_kyleStrategy` + the 3 consumers); the only other build output is the pre-existing `ring`→`ring_nf` INFO at Regularity.lean:57. `#print axioms` on `isGammaSolution_zero_iff`, `existsUnique_zeroSolution`, `gamma_eq_half` and `Monotone.eq_of_ae_eq_continuous` all `[propext, Classical.choice, Quot.sound]` (verified twice: in-tree in the AxiomAudit log, and out-of-tree from a scratch file). Explicit lint pass `lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true KyleUniqueness/Main.lean` prints only the `sorry` warning; all lines in all four edited files ≤ 99 chars by a UTF-8-aware count.

EXTRA VERIFICATION (out of tree, all six compiled). Non-vacuity: `gamma_eq_half isGammaSolution_zero_id : noiseTraderLoss id = 1/2`, agreeing with the independently-proved `noiseTraderLoss_id`. Real work: `existsUnique_zeroSolution.unique h ((isGammaSolution_zero_iff id).2 rfl)` derives `ψ = id` from a bare `IsGammaSolution 0 ψ`. Helper on a genuine instance: a monotone `f` a.e.-equal to `(· + 3)` has `f 7 = 10`. Helper non-vacuous at `id`. Pair form still elaborates against `stdModel`.

FAITHFULNESS. I re-read v4 Prop 6.1 (paper/v4.txt:635) and Thm 7.1 (:762) line by line against the Lean. The Theorem 7.1 proof's four steps — Lemma 2.4 strict monotonicity, Props 6.1+4.1 giving `φ = v + a` a.e., the increasing+continuous upgrade to everywhere, and Gaussian regression `F(x) = (x−a)/2` followed by the unique-maximiser comparison forcing `a = 0` — map one-to-one onto `strictMono_of_isGammaSolution`/`monotone_of_isGammaSolution`, `gamma_eq_half` + `noiseTraderLoss_eq_half_iff`, `Monotone.eq_of_ae_eq_continuous`, and `gaussianSmoothing_affine` + the `h.2 0 (a/2)` comparison. No hypothesis beyond the paper's was added anywhere.

**Gotchas:**
Pin-specific facts worth banking in PROVING_LOG.md (I did not edit it — rule 1 restricts this wave's edits to the five files above).

1. `lt_or_le`, `eventually_lt_const`, `Iio_mem_nhds`/`Ioi_mem_nhds` (the *point* versions) DO NOT EXIST at this pin. `Iio_mem_nhds` exists only inside `Mathlib/Topology/Algebra/WithZeroTopology.lean` (namespaced, wrong type class). The portable spelling for "a set cut out by a strict inequality is a neighbourhood" is `isOpen_Iio.mem_nhds h` / `isOpen_Ioi.mem_nhds h` via `IsOpen.mem_nhds` (Mathlib/Topology/Neighborhoods.lean:90).

2. To turn `ContinuousAt` into a neighbourhood fact, use `ContinuousAt.preimage_mem_nhds` (Mathlib/Topology/Continuous.lean:72): `hg.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hcon) : g ⁻¹' Iio c ∈ 𝓝 v`. Applying the `Tendsto` directly to a set membership (`hg.continuousAt hs`) relies on the filter-`≤` unfolding and is not worth the risk; and there is no `Metric` detour needed at all.

3. `mem_nhds_iff_exists_Ioo_subset` (Mathlib/Topology/Order/Basic.lean:507, needs `[NoMaxOrder] [NoMinOrder]`, ℝ qualifies) is the right way to extract a two-sided open interval from a neighbourhood. It gives `∃ l u, a ∈ Ioo l u ∧ Ioo l u ⊆ s` — note `a ∈ Ioo l u` destructures as `⟨hlv, hvu⟩`, so both sides of `v` come out of one call and the *same* interval serves both halves of an `le_antisymm`.

4. "Null complement ⇒ meets every open interval" is 5 lines at this pin: `measure_mono_null hsub hnull` then `rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hle; linarith`. `Real.volume_Ioo : volume (Ioo a b) = ofReal (b − a)` lives in `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean:96` INSIDE `namespace Real` (so it is `Real.volume_Ioo`, not the bare `volume_Ioo` the grep line suggests), and `ENNReal.ofReal_eq_zero : ofReal p = 0 ↔ p ≤ 0` is `Mathlib/Data/ENNReal/Real.lean:181`. No `Dense`/`measure_pos_of_nonempty_interior` machinery is needed.

5. `ae_iff.1 hae` converts `f =ᵐ[μ] g` to `μ {x | ¬ f x = g x} = 0` (`Mathlib/MeasureTheory/OuterMeasure/AE.lean:78`). Using it explicitly rather than relying on the `EventuallyEq`→`ae`-filter defeq keeps the `by_contra` set-inclusion step matching syntactically.

6. `sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0` exists (`Mathlib/Algebra/GroupWithZero/Basic.lean:262`) but `pow_eq_zero_iff` does NOT grep as a `theorem` at this pin. The idiom `exact sq_eq_zero_iff.1 (le_antisymm hsq (sq_nonneg a))` is how you get an EQUALITY out of `nlinarith`, which can only deliver the inequality `a ^ 2 ≤ 0`.

7. Declaring a dotted helper inside `namespace KyleUniqueness` (here `Monotone.eq_of_ae_eq_continuous`, full name `KyleUniqueness.Monotone.eq_of_ae_eq_continuous`) matches the repo's existing convention (`NullSingletonClass.withDensity` in GaussianHelpers.lean:183). In AxiomAudit, write such a name FULLY QUALIFIED in the `#print axioms` line — `open KyleUniqueness` plus a root namespace that Mathlib also populates (`Monotone`) is exactly the shape that produces an ambiguity error the day someone upstreams a same-named lemma.

8. `lake env lean` still does not run the style linters (confirmed again). The lint-bearing command remains `lake build <module>` from a deleted olean, or `lake env lean -Dweak.linter.mathlibStandardSet=true …`; I ran both on Main.lean and both print only the expected `sorry` warning.

9. The only pre-existing build noise in the tree is the `ring`→`ring_nf` INFO at `Regularity.lean:57`. After this wave it is the only non-`#print axioms` `info:` line in a full build log — useful as the canary that the linters are actually firing.

### Stage B (location–scale) — route
ROUTE CHOSEN: neither of the two suggested routes verbatim — a third, strictly cheaper variant of Route 1 that I'll call "Route 1-prime (law-level standardisation, no auxiliary KyleModel)". Documented in the new Main.lean section docstring at KyleUniqueness/Main.lean:190-222.

WHY: Route 1's expensive parts are exactly the ones that need a second KyleModel — building `M.standardised` (laws + IndepFun.comp), proving `flowSigma` equality through a `comap` of the measurable equivalence `y ↦ y/σ`, transporting `condExp` (`condExp_sub`/`condExp_smul`/`condExp_const`), and then REPLAYING the whole `key` computation of `equilibrium_iff_zeroSolution` at a general standardised Ω (step (b), ~100 LOC). None of that is needed: the argument never touches the standardised probability space, only the standardised LAWS, and `N(μ₀,τ²)`, `N(0,σ²)` are push-forwards of `N(0,1)` under `t ↦ μ₀+τt` and `s ↦ σs`. So §7's change of variables happens entirely inside two Bochner integrals on the ORIGINAL model M, and the σ-algebra / conditional-expectation transport disappears.

THE CHAIN (all new, all in KyleUniqueness/Main.lean, namespace KyleUniqueness.KyleModel):
1. `map_std_valueLaw` / `map_std_noiseLaw` — the two push-forward identities, via `gaussianReal_map_const_mul` + `gaussianReal_map_const_add` (and `Measure.map_map` for the composite). `integral_valueLaw_std` / `integral_noiseLaw_std` turn them into `integral_map` change-of-variables.
2. `flowPDF_mul_sigma` : `p_φ(σy) = p̂_φ̂(y)/σ`, and `flowNum_mul_sigma` : `n_φ(σy) = (μ₀·p̂(y) + τ·n̂(y))/σ`. Both are `integral_valueLaw_std` + the single analytic input, a private lemma `gaussianPDFReal_mul_of_pos : gaussianPDFReal 0 v (s*z) = gaussianPDFReal 0 1 z / s` when `(v:ℝ) = s^2`, `0 < s`.
3. `bayesPrice` := `flowNum/flowPDF` (the general-M Bayes quotient) with `flowPDF_pos` (Lemma 2.1 positivity at general (μ₀,τ,σ), obtained FROM `flowPDF_mul_sigma` + `lemma21_flowDensity_pos` — no re-proof), `measurable_flowNum`, `measurable_bayesPrice`, and `isPricingRule_bayesPrice` via the existing general-M `isPricingRule_of_forall_mul_flowPDF`.
4. `bayesPrice_mul_sigma` : `P₀(σy) = μ₀ + τ·inverseRegression φ̂ (y)` — i.e. §7's `P̂(y) = (P(σy)−μ₀)/τ` IS §2's normalised inverse regression of φ̂, pointwise (everywhere, not a.e.).
5. `integrable_bayesPrice_comp` / `integral_bayesPrice_comp` : `E[P₀(σx+U)] = μ₀ + τ·F̂(x)`, pushing along U through `map_U` then `map_std_noiseLaw`; the L¹ input is a private `integrable_inverseRegression_shift` factored out of the proof of `equilibrium_iff_zeroSolution` (`lemma23_integrable` + `Integrable.comp_add_right` + `integrable_gaussianReal_iff`).
6. `expectedProfit_bayesPrice` : `M.expectedProfit P₀ (μ₀+τv) (σx) = στ · objective 0 φ̂ v x` — v4 §7's "expected profits are multiplied by the positive constant στ", exactly.
7. `isEquilibrium_eq_kyleStrategy`: `pricingRule_ae_eq_of_flowPDF_pos` (general M, already in CondExpBridge) + `expectedProfit_congr_ae` move the maximisation hypothesis from the arbitrary pricing rule supplied by `IsEquilibriumStrategy` onto `P₀`; instantiate `hmax` at `(μ₀+τv, σx)`, rewrite `φ(μ₀+τv) = σ·φ̂(v)` by `mul_stdStrategy`, divide by `στ > 0` (`le_of_mul_le_mul_left`) to get `IsGammaSolution 0 φ̂`; then Theorem 7.1 (`isGammaSolution_zero_iff`) gives `φ̂ = id`, and evaluating at `t = (v−μ₀)/τ` gives `φ v = (σ/τ)(v−μ₀) = M.kyleStrategy v`.

NOT USED (and not needed): `IndepFun.comp`, `MeasurableSpace.comap_comp`, `condExp_sub`/`condExp_smul`/`condExp_const`, any MeasurableEquiv, `indepFun_iff_map_prod_eq_prod_map_map`, and any replay of `equilibrium_iff_zeroSolution` at general Ω. `equilibrium_iff_zeroSolution` itself is NOT used by the final proof — the new chain subsumes it (it remains in Statement.lean as the σ=τ=1 faithfulness certificate).

SCOPE: Statement.lean, KyleUniqueness.lean (root), Accounting.lean and SignedRoot.lean were NOT touched — no duplicate names arose, and everything the standardisation needed was already exported. Only Main.lean (+250 LOC: 350 → 600) and AxiomAudit.lean (prose + 18 new `#print axioms` lines) changed.

FINAL GATE: full clean rebuild after `rm -rf .lake/build/lib/lean/KyleUniqueness` — "Build completed successfully (3149 jobs)", 26 s, exit 0, ZERO warnings, ZERO errors, ZERO `sorryAx` anywhere in the build log, ZERO "declaration uses sorry". `grep -rn "sorry" KyleUniqueness/*.lean` finds only docstring/comment prose. An out-of-tree probe file (imports KyleUniqueness.Main) additionally checks non-vacuity (`kyleStrategy_isEquilibrium M` inhabits the hypothesis class; `kyle_existsUnique_equilibrium M` typechecks), the `stdModel` specialisation (`φ = id`), and that `stdModel.stdStrategy φ = φ` / `stdModel.bayesPrice φ = inverseRegression φ` (the standardisation is the identity on the normalised model) — all pass, and `#print axioms` on the four headline names out of tree gives `[propext, Classical.choice, Quot.sound]`.

**Gotchas:**
NEW pin-specific gotchas from this wave (worth adding to PROVING_LOG):

1. **`Measurable.add` / `Measurable.const_add` feed a Pi-level function into `integral_map`'s `φ`.** Writing `integral_map (measurable_const.add (measurable_const_mul M.τ)).aemeasurable …` makes Lean unify the map as `(fun x => M.μ₀) + fun x => M.τ * x`, and the subsequent `rw [M.map_std_valueLaw]` then fails with "Did not find an occurrence". This is the same family as Wave-1's `Integrable.sub` gotcha, but it bites through a lemma ARGUMENT rather than through `rw`. FIX: always bind an explicit-lambda `have hmap : Measurable (fun t : ℝ => M.μ₀ + M.τ * t) := by fun_prop` first and pass `hmap.aemeasurable`.

2. **`⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0` in a lemma STATEMENT is a trap.** `simp only [gaussianPDFReal, NNReal.coe_mk]` will NOT reduce `↑⟨s ^ 2, ⋯⟩` inside `√(2 * π * ↑⟨s^2, ⋯⟩)` — the elaborator reports the coercion at type `{ r // 0 ≤ r }` rather than `NNReal`, and `rw` then can't see the pattern (the error even carries a "target expression is not type-correct under `instances` transparency" note). FIX: never put the anonymous constructor in the statement. Parameterise instead: `{v : NNReal} (hv : (v : ℝ) = s ^ 2)`, prove everything by `rw [hv]`, and discharge the hypothesis at call sites with a bare `rfl` (`gaussianPDFReal_mul_of_pos M.hσ (v := M.noiseVar) rfl`) — this also removes the need to `rw [M.noiseVar_def]` first.

3. **`congr 1` on `gaussianReal a u = gaussianReal b w` leaves an `ℝ≥0` goal that `rw [mul_one]` does not close by `rfl`.** The residue `NNReal.mk (M.τ ^ 2) ⋯ = M.valueVar` needs `exact M.valueVar_def.symm` (proof irrelevance is fine for `exact`, not for `rw`'s trailing `rfl`).

4. **`ring` emitting a bare "Try this: [apply] ring_nf" with NO source position, exit code 0.** This is `ring` failing, falling back to `ring_nf`, succeeding, and logging a suggestion. It is silent about where. Bisecting by truncating a copy of the file and running `lake env lean` on the copy is the fastest way to localise it. In my case the cause was `rw [h1, h2, mul_one]` where `mul_one` fired on `2 * 1` in the exponent instead of on `2 * π * 1` inside the `√`, leaving `√(2*π)` vs `√(2*π*1)` — atoms `ring` cannot identify. FIX: fold `mul_one` into the preceding `simp only` and restate the helper with `/ 2` instead of `/ (2 * 1)`. NOTE: there is a PRE-EXISTING instance of this message from `Regularity.lean:57` (already documented as gotcha #14); it is not from this wave's code and Regularity.lean was outside my edit scope.

5. **`linter.style.show` fires on `show φ v = M.σ / M.τ * (v - M.μ₀)` even when it is a pure defeq unfold of `M.kyleStrategy v`.** `lake env lean` does NOT show it (gotcha #1 again — only `lake build` applies `weak.linter.mathlibStandardSet`). FIX: `have hks : M.kyleStrategy v = M.σ / M.τ * (v - M.μ₀) := rfl` then `rw [hks]`.

6. **`div_eq_div_iff` orientation at this pin**: `div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b` (Mathlib/Algebra/GroupWithZero/Units/Basic.lean:468) — note the RHS is `a * d = c * b`, NOT `a * d = b * c`. Pair it with `linear_combination` rather than `linarith`, since `linarith` treats `(v - μ₀) * σ` and `σ * (v - μ₀)` as distinct atoms.

7. `Integrable.const_add` does NOT exist at this pin (only `integrable_const_add_iff`, and that needs `IsFiniteMeasure`); use `(integrable_const c).add h` bound to a type-ascribed explicit-lambda `have`. `Integrable.congr (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ` does exist (L1Space/Integrable.lean:122).

8. `MeasureTheory.integral_pos_iff_support_of_nonneg_ae` lives in `Integral/Bochner/Basic.lean:747`; a grep for `theorem integral_pos_iff_support_of_nonneg_ae` hits the interval-integral homonym in `IntervalIntegral/Basic.lean` FIRST. (I ended up not needing it — `flowPDF_pos` comes for free from `flowPDF_mul_sigma` + `lemma21_flowDensity_pos`, which is a better pattern than re-proving positivity at general M.)

9. `integral_div (r) (f) : ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r` and `integral_const_mul` are UNCONDITIONAL (they are `integral_smul` in disguise) — no integrability side-goals, which is what makes the `*_mul_sigma` proofs 10 lines each.

10. Reusing `stdModel`'s general-M lemmas at the standard laws works cleanly via `rw [stdModel_noiseVar, stdModel_valueLaw] at h` (e.g. `stdModel.integrable_noisePDF_comp` / `integrable_id_mul_noisePDF_comp` become the `gaussianReal 0 1` statements), and the result then `exact`s against a `stdNormalPDF`-spelled goal by defeq. Cheaper than re-proving the dominated-convergence bounds.

### Final audit — faithfulness ledger (verbatim from the auditor)
- NON-BLOCKING, DELIBERATE ROUTE DIFFERENCE (Lane-C decision D7), but it is the single largest divergence from the paper's current text and MUST be disclosed: v4 Lemma 2.7 (Cacoullos lower Gaussian variance bound, (E[f'(V)])^2 <= Var f(V)) has NO Lean counterpart anywhere in the tree. The step it serves in v4's proof of Prop 6.1 -- namely 1 <= 2*Gamma -- is proved instead by the v3 one-sided Stein inequality `one_le_sqrt_integral_sq_mul_integral_inv_sq` (KyleUniqueness/SteinInequality.lean), whose statement is: Monotone f, a.e. HasDerivAt f (f' x) x, a.e. 0 < f' x, Integrable f^2, Integrable (f')^{-2} => 1 <= sqrt((int f^2 dgamma) * (int (f')^{-2} dgamma)). Consequence: the formalized proof of v4 Prop 6.1 is v3's proof, not v4's. Anything published must say 'we formalize the v3 route for this one step', not 'we formalize the paper'.
- NON-BLOCKING, DEFINIENS DIFFERS: paper v4 sec.3.1 DEFINES Gamma := E[U(P(Y) - V)]. Lean DEFINES `noiseTraderLoss phi := int p.2 * inverseRegression phi (phi p.1 + p.2) d(gamma (x) gamma)` = E[U*P(Y)], which is the paper's SECOND expression (an equality proved in its Lemma 3.1, not its definition). The gap is fully bridged inside the artifact: `integral_noise_mul_sub_value_eq_noiseTraderLoss` proves int U*(P(Y)-V) = noiseTraderLoss phi (the paper's literal definiens) and `covariance_noise_condExp_eq_noiseTraderLoss` proves covariance U (mu[V|flowSigma phi]) mu = noiseTraderLoss phi (the paper's Cov form). No content is lost; the starting point differs.
- NON-BLOCKING BUT REAL WEAKENING vs the paper's wording: v4 Lemma 2.3 (version clause), Lemma 3.1 and Lemma 3.2 are each stated in the paper 'for every Borel version P-tilde of the inverse regression'. Every Lean rendering is stated for the ONE canonical continuous version `inverseRegression phi` (the Bayes quotient). There is no single Lean lemma reading 'Gamma = E[U * P-tilde(Y)] for every Borel version P-tilde', nor 'Pi(v) = E[(v - P-tilde(phi v + U)) phi v] for every Borel version'. The transfer machinery EXISTS and IS used on the headline path -- `KyleModel.pricingRule_ae_eq_of_flowPDF_pos` (any two pricing rules for the same phi agree Lebesgue-a.e. once p_phi > 0), `expectedProfit_congr_ae` (profits are insensitive to Lebesgue-null modification), `lemma21_unique_continuous_version`, and `equilibrium_iff_zeroSolution` (which existentially quantifies the pricing rule) -- so the paper's every-version content is recoverable by composing two lemmas, but it is never stated as one.
- NON-BLOCKING, DOCUMENTED MATHLIB GAP: v4 Lemma 2.2's clause 'by Lemma 2.1 and Bayes' formula, y |-> pi_y is a version of the conditional law of V given Y = y' is NOT formalized. `ProbabilityTheory.condDistrib` appears nowhere in the tree except in two explanatory docstrings (Definitions.lean:210, Resampling.lean:21). What IS proved are the consequences actually used: `posterior` is a probability measure (`isProbabilityMeasure_posterior`), `inverseRegression_eq_integral_posterior` (P(y) = int v dpi_y), `memLp_id_posterior`, `memLp_strategy_posterior`, and the joint-law identity `map_value_orderFlow`.
- NON-BLOCKING PARTIAL RENDERING: v4 Lemma 2.5 asserts 'the function P is CONTINUOUSLY differentiable'. Lean proves differentiability everywhere (`hasDerivAt_inverseRegression`), the covariance formula (`deriv_inverseRegression_eq_cov`, eq. (2.7)) and strict positivity (`deriv_inverseRegression_pos`), but there is NO declaration asserting `Continuous (deriv (inverseRegression phi))` -- grep over the tree finds only deriv_inverseRegression_eq_cov / _eq_symm / _pos. The corresponding C^1 clause for F IS fully rendered (`continuous_deriv_gaussianSmoothing`). Nothing downstream consumes continuity of P', so this is a wording gap, not a hole.
- NON-BLOCKING, DELIBERATE CONSTRUCTION DIFFERENCE (Lane-C decision D4): v4 Lemma 2.6 builds V^(1) 'on an extension of the underlying probability space' via Kallenberg's transfer theorem and states that V^(0), V^(1) are conditionally i.i.d. given Y. Lean instead constructs an explicit measure `resamplingMeasure phi` on R^3 by one flat `withDensity` with density rho(v0)rho(y-phi v0)rho(v1)rho(y-phi v1)/p(y), and the conditional-independence statement itself is never formalized. Clauses (i)-(iv) are rendered as: (i) `resamplingMeasure_map_swap` (invariance under (v0,v1,y) |-> (v1,v0,y)); (ii) `resamplingMeasure_map_snd` and `resamplingMeasure_map_fst` (both the (v1,y) and (v0,y) marginals equal volume.withDensity rho(.)rho(.-phi .)), matching `map_value_orderFlow`; (iii) `integral_v1_mul_eq_inverseRegression` and (iv) `integral_v1_mul_comp_eq_gaussianSmoothing` / `integral_v1_mul_eq_gaussianSmoothing`, both in BOUNDED-TEST-FUNCTION form against measurable g with |g| <= C, NOT as `condExp` equalities. Given `integrable_v1_resampling`, the test-function form against all bounded measurable g is equivalent to the conditional-expectation statement, so nothing downstream is weakened.
- NON-BLOCKING, DELIBERATE (Lane-C decision D2): v4 Lemma 2.4 works with W(v) := sup_x x(v - F(x)) with the value +infinity allowed, and separately asserts 'W is nonnegative because x = 0 is admissible, and convex because it is a pointwise supremum of affine functions' BEFORE assuming pointwise maximisation. Lean DEFINES `insiderProfit phi v := objective 0 phi v (phi v) = phi v * (v - F(phi v))` -- the attained value, total and real-valued by construction -- so 'W is real-valued' is true by fiat rather than proved of the sup. The faithfulness bridge is present and mandatory-by-decision: `insiderProfit_eq_iSup : IsGammaSolution 0 phi -> forall v, insiderProfit phi v = iSup (objective 0 phi v)`. Corollary of the choice: `insiderProfit_nonneg` and `convexOn_insiderProfit` both carry the hypothesis `IsGammaSolution 0 phi`, whereas the paper has them for arbitrary phi. Every consumer supplies that hypothesis, so nothing downstream needs the general form.
- NON-BLOCKING, HYPOTHESIS THE PAPER DOES NOT DISPLAY: `kyle_equilibrium_pair_iff` takes an explicit `(hP : Measurable P)`. The paper folds this into its standing sentence 'market makers ... set the price P(Y_phi), where P : R -> R is a Borel-measurable pricing rule'. It is genuinely needed for the <= direction, because the right-hand side (1.1) /\ (1.2) does not by itself say P is Borel; in the => direction it is redundant (IsEquilibrium.pricingRule.measurable already gives it). Verdict: faithful, but a reader comparing the Lean line to the paper's one-sentence Theorem 1.1 will see one extra hypothesis.
- NON-BLOCKING, REDUNDANT HYPOTHESIS: `accounting_identity` takes `Measurable phi` in addition to `Monotone phi`, while v4 Prop 5.1 states only 'if phi is nondecreasing and Pi(V) >= 0 almost surely'. A monotone R -> R is automatically Borel, so the extra hypothesis is redundant; it is also always available at the call sites. Harmless, but it makes the Lean statement formally weaker than the paper's.
- NOT A DEFECT, RECORDED FOR THE LEDGER (Lean is STRONGER): v4 Prop 6.1 hypothesises '(phi, P) is an equilibrium in the normalised model'; Lean's `gamma_eq_half` hypothesises `IsGammaSolution 0 phi`, i.e. only the pointwise-maximisation condition against the canonical F -- which is the first line of the paper's own proof of Prop 6.1 and is strictly weaker than equilibrium (equilibrium => IsGammaSolution via `equilibrium_iff_zeroSolution`). Same for v4 Thm 7.1 vs `isGammaSolution_zero_iff`. No loss.
- NON-BLOCKING SCOPE EXCLUSION: v4 Appendix B ('From almost-everywhere to pointwise maximisation', the footnote-1 variant in which profit maximisation is imposed only for Lebesgue-a.e. v and the equilibrium strategy is unique modulo null sets) is NOT formalized. This was explicitly deferred as optional post-headline content (blueprint attack_order Tier 5, node R3). Any claim text must scope Theorem 1.1 to the pointwise-maximisation definition.
- NON-BLOCKING, ROUTE DIFFERENCE IN sec.7: the paper proves Theorem 1.1 by a change of variables that literally standardises the probability space (V-hat := (V-mu)/tau, U-hat := U/sigma) and asserts '(phi,P) is an equilibrium iff (phi-hat, P-hat) is an equilibrium of the standardised model'. Lean never builds the standardised KyleModel; it standardises only the LAWS (`KyleModel.map_std_valueLaw`, `KyleModel.map_std_noiseLaw`) and pushes sec.7 through two Bochner integrals (`flowPDF_mul_sigma`, `flowNum_mul_sigma`, `bayesPrice_mul_sigma`, `expectedProfit_bayesPrice`: E[(mu0+tau*v - P0(sigma*x+U))*sigma*x] = sigma*tau*objective 0 phi-hat v x). The equilibrium-transfer biconditional of sec.7 is therefore never stated; only the direction the headline needs is proved. Documented in Main.lean's 'Route taken' block.

**Other findings:**
- === FAITHFULNESS LEDGER (paper v4 result -> Lean declaration(s) -> deviation). Deviations are spelled out in the faithfulness_issues field; tags F1-F12 below refer to them in order. === | v4 THEOREM 1.1 (pair form) -> `kyle_equilibrium_pair_iff (M) (phi P) (hP : Measurable P) : M.IsEquilibrium phi P <-> phi = M.kyleStrategy /\ forall-ae w dM.mu, P (M.orderFlow phi w) = M.mu0 + M.priceImpact * M.orderFlow phi w`. Supporting forms: `kyle_unique_equilibrium` (strategy iff), `kyle_existsUnique_equilibrium` (exists-unique), `isEquilibrium_eq_kyleStrategy` (uniqueness half), `kyleStrategy_isEquilibrium` + `kyleStrategy_kylePricingRule_isEquilibrium` (existence halves), `pricingRule_ae_eq_kylePricingRule` + `eq_kylePricingRule_of_continuous` (eq. (1.2) rigidity). Checked term by term against v4 sec.1: `kyleStrategy = fun v => sigma/tau*(v-mu0)` = (1.1) and function equality carries 'for every v'; `priceImpact = tau/(2*sigma)` and the a.e. clause along the order flow = (1.2); `IsEquilibrium` = Measurable phi /\ IsPricingRule phi P /\ forall v x, expectedProfit P v x <= expectedProfit P v (phi v), which is items 1 and 2 of sec.1 verbatim, with the quantifier 'for every v' and no regularity or moment hypothesis on phi beyond Borel. DEVIATIONS: F8 (explicit Measurable P), F12 (sec.7 route), F3 (version quantifier).
- LEDGER (cont.) | v4 THEOREM 7.1 (Rigidity) -> `isGammaSolution_zero_iff (phi) : IsGammaSolution 0 phi <-> phi = id`, with `existsUnique_zeroSolution : exists-unique phi, IsGammaSolution 0 phi`. `IsGammaSolution 0 phi` unfolds to `Measurable phi /\ forall v x, objective 0 phi v x <= objective 0 phi v (phi v)` with `objective 0 phi v x = x * (v - gaussianSmoothing phi x)` -- exactly 'phi(v) in argmax_x (x*v - x*F_phi(x)) for every v'. Both directions proved (the converse via `gaussianSmoothing_id : gaussianSmoothing id = fun x => x/2` and a strict-concavity nlinarith). DEVIATION: F11 -- the paper quantifies F_phi over ANY Borel version P_phi; Lean fixes the canonical `inverseRegression`. The paper's exact form is recovered only by composing with `equilibrium_iff_zeroSolution`.
- LEDGER (cont.) | v4 PROPOSITION 4.1 (covariance bound + equality cases) -> `noiseTraderLoss_le_half (hphi : Measurable phi) : |noiseTraderLoss phi| <= 1/2` (= (4.1), both bounds in one absolute value), `noiseTraderLoss_eq_half_iff : Measurable phi -> (noiseTraderLoss phi = 1/2 <-> exists a, phi =ae[volume] fun v => v + a)`, `noiseTraderLoss_eq_neg_half_iff` with `fun v => -v + a`, and `integrable_noiseTraderLoss` for the well-definedness the paper asserts in Lemma 3.1. Hypothesis is Measurable phi ONLY, matching the paper's 'over all Borel-measurable insider strategies'. NO DEVIATION -- this is the closest match in the artifact.
- LEDGER (cont.) | v4 PROPOSITION 5.1 (accounting identity) -> `accounting_identity (hphi : Measurable phi) (hmono : Monotone phi) (hnn : forall-ae v dgamma, 0 <= insiderProfit phi v) : Integrable (insiderProfit phi) gamma /\ noiseTraderLoss phi = int insiderProfit phi v dgamma`. Specialised for the consumer as `integrable_insiderProfit_of_isGammaSolution` and `noiseTraderLoss_eq_integral_insiderProfit`. The paper's sec.5 Part I symmetric representation is `replica_identity : Measurable phi -> 2 * noiseTraderLoss phi = int (phi q.1 - phi q.2.1) * (q.1 - q.2.1) d(resamplingMeasure phi)`; the lattice truncation is `clampAt` + `clamp_increment_bounds` + `tendsto_clamp_replica` + `ae_clamp_insiderProfit`. DEVIATION: F9 (redundant Measurable phi).
- LEDGER (cont.) | v4 PROPOSITION 6.1 (covariance saturation) -> `gamma_eq_half (h : IsGammaSolution 0 phi) : noiseTraderLoss phi = 1/2`, assembled from `one_le_two_mul_noiseTraderLoss` (1 <= 2*Gamma) and `noiseTraderLoss_le_half` (Gamma <= 1/2) by linarith. The unnumbered construction inside the paper's proof is KyleUniqueness/SignedRoot.lean: c := F(0) is `criticalPoint` with `strategy_criticalPoint` (phi(c) = 0) and the two sign lemmas; q(v) := F'(phi v) is `posteriorSlope` with `posteriorSlope_pos` and `noiseTraderLoss_eq_integral_posteriorSlope` (Gamma = E[q(V)]) and `noiseTraderLoss_pos` (Gamma > 0); h(v) := sign(v-c)*sqrt(2W(v)) is `signedRoot` with `signedRoot_sq` (h^2 = 2*Pi), `ae_hasDerivAt_signedRoot` (h' = rootSlope a.e.), `inv_rootSlope_sq` ((h')^{-2} = 2q), `integral_sq_signedRoot` (E[h(V)^2] = 2*E[Pi(V)]) and `integral_inv_sq_rootSlope` (E[1/h'(V)^2] = 2*Gamma). DEVIATIONS: F1 (Stein instead of Cacoullos -- the ONLY place the formalized proof is v3's rather than v4's), F10 (weaker hypothesis, Lean is stronger).
- LEDGER (cont.) | v4 LEMMA 2.1 -> joint density: `map_value_orderFlow (hphi) : map (fun p => (p.1, phi p.1 + p.2)) (gamma (x) gamma) = volume.withDensity (jointDensity phi)` with `jointDensity phi p = ENNReal.ofReal (stdNormalPDF p.1 * stdNormalPDF (p.2 - phi p.1))` -- literally rho(v)rho(y - phi(v)). Everywhere-positive p_Y: `lemma21_flowDensity_pos (hphi) : forall y, 0 < flowDensity phi y` where `flowDensity phi y = int stdNormalPDF (y - phi v) dgamma`. Law of Y: `KyleModel.map_orderFlow (hphi) : map (M.orderFlow phi) M.mu = volume.withDensity (fun y => ENNReal.ofReal (M.flowPDF phi y))`, with `KyleModel.flowPDF_pos` at general (mu0, tau, sigma). NO DEVIATION. | v4 LEMMA 2.2 -> `lemma21_continuous` (P continuous), `lemma21_isPricingRule (hphi) : stdModel.IsPricingRule phi (inverseRegression phi)` (P(Y) = E[V|Y] a.s., for EVERY Borel phi -- definitional-fidelity canary), `lemma22_memLp_two` (P(Y) in L^2), plus `posterior` / `isProbabilityMeasure_posterior` / `inverseRegression_eq_integral_posterior` for pi_y. Uniqueness of the continuous version: `lemma21_unique_continuous_version`. DEVIATION: F4.
- LEDGER (cont.) | v4 LEMMA 2.3 -> finiteness of (2.1): `integrable_inverseRegression_const_add (hphi) : forall x, Integrable (fun u => inverseRegression phi (x+u)) gamma`; C^1: `hasDerivAt_gaussianSmoothing` + `continuous_deriv_gaussianSmoothing`; (2.2): `gaussianSmoothing_eq_convolution : gaussianSmoothing phi x = int inverseRegression phi y * stdNormalPDF (y-x)`; (2.3) first form: `deriv_gaussianSmoothing : deriv (gaussianSmoothing phi) x = int P(y)*((y-x)*rho(y-x))`; (2.3) second form: `deriv_gaussianSmoothing_eq_integral : ... = int u * P(x+u) dgamma`, with `deriv_gaussianSmoothing_comp_eq` for the composed version; absolute convergence: `lemma23_integrable`; version clause (P-tilde(x+U) in L^1, E = F(x)): `KyleModel.integrable_Q_comp_add` + `expectedProfit_congr_ae` + `KyleModel.pricingRule_ae_eq_of_flowPDF_pos`; tower clause F(phi(V)) = E[E[V|Y]|V]: `gaussianSmoothing_comp_ae_eq_condExp_condExp`. DEVIATION: F3 (version clause is machinery, not a single statement).
- LEDGER (cont.) | v4 LEMMA 2.4 -> W real-valued + attainment: `insiderProfit` (def) + `insiderProfit_eq_iSup`; (2.4) FOC: `firstOrderCondition (h) : forall v, F(phi v) + phi v * F'(phi v) = v`; (2.5): `insiderProfit_eq_sq_mul_deriv (h) : forall v, insiderProfit phi v = phi v ^ 2 * deriv (gaussianSmoothing phi) (phi v)`; (2.6) W' = phi a.e.: `ae_hasDerivAt_insiderProfit (h) : forall-ae v, HasDerivAt (insiderProfit phi) (phi v) v`; local absolute continuity: `insiderProfit_sub_eq_intervalIntegral (h) : forall a b, insiderProfit phi b - insiderProfit phi a = int_a^b phi`; phi strictly increasing: `strictMono_of_isGammaSolution`, with `monotone_of_isGammaSolution` for Prop 5.1; (A.1) subgradient: `insiderProfit_subgradient`; convexity/nonnegativity: `convexOn_insiderProfit`, `insiderProfit_nonneg`. DEVIATION: F7. | v4 LEMMA 2.5 -> `memLp_id_posterior`, `memLp_strategy_posterior` (id, phi in L^2(pi_y)); (2.7): `deriv_inverseRegression_eq_cov` (P'(y) = E_pi[id*phi] - E_pi[id]*E_pi[phi]) and `deriv_inverseRegression_pos (hphi) (hmono : StrictMono phi)`; (2.8): `deriv_gaussianSmoothing_pos` / `deriv_gaussianSmoothing_pos_of_strictMono`; strict monotonicity of P and F: `strictMono_inverseRegression`, `strictMono_gaussianSmoothing(_of_strictMono)`. DEVIATIONS: F5 (C^1 of P only partially); hypothesis decoupled to an explicit `StrictMono phi` instead of 'under the hypothesis of Lemma 2.4' (a generalisation, supplied at every call site by `strictMono_of_isGammaSolution`).
- LEDGER (cont.) | v4 LEMMA 2.6 -> `resamplingMeasure` + `isProbabilityMeasure_resamplingMeasure`; (i) `resamplingMeasure_map_swap`; (ii) `resamplingMeasure_map_snd` and `resamplingMeasure_map_fst` (both equal volume.withDensity rho(r.1)rho(r.2 - phi r.1), which by `map_value_orderFlow` is the law of (V,Y)), with `resamplingMeasure_map_v0`/`_v1` (both marginals standard normal) and `resamplingMeasure_map_y`; (iii) `integral_v1_mul_eq_inverseRegression`; (iv) `integral_v1_mul_comp_eq_gaussianSmoothing` and `integral_v1_mul_eq_gaussianSmoothing`; integrability side conditions `integrable_v1_resampling`, `integrable_v0_resampling`, `integrable_v0_mul_v1_resampling`. DEVIATION: F6. | v4 LEMMA 2.7 -> NO COUNTERPART; see F1. | v4 LEMMA 3.1 -> `noiseTraderLoss` (def) + `integrable_noiseTraderLoss` (well defined and finite); Gamma = E[U(P-tilde(Y)-V)]: `integral_noise_mul_sub_value_eq_noiseTraderLoss`; = Cov(U, E[V|Y]): `covariance_noise_condExp_eq_noiseTraderLoss`; = E[F'(phi(V))]: `noiseTraderLoss_eq_integral_deriv`, with `integrable_deriv_gaussianSmoothing_comp`. DEVIATIONS: F2, F3. | v4 LEMMA 3.2 -> `insiderProfit` + `insiderProfit_apply : insiderProfit phi v = phi v * (v - gaussianSmoothing phi (phi v))` (finite-valued by construction, R-valued), `measurable_insiderProfit` (Borel), and `expectedProfit_inverseRegression` / `objective_eq_expectedProfit` for Pi(v) = E[(v - P(phi v + U)) phi v]. DEVIATION: F3.
- BUILD EVIDENCE (item 1 of the brief). Ran `rm -rf .lake/build/lib/lean/KyleUniqueness .lake/build/lib/lean/KyleUniqueness.{olean,olean.hash,ilean,ilean.hash,trace}` -- ONLY the project's own build output; `.lake/packages` untouched, confirmed by `git status --porcelain` showing exactly the 4 modified + 1 untracked project files before and after. Then a bare `lake build`: EXIT 0, 'Build completed successfully (3149 jobs)', 25 s wall, all 18 project modules rebuilt from source ('Built KyleUniqueness.Statement (2.9s)' ... 'Built KyleUniqueness.Main (1.8s)' ... 'Built KyleUniqueness.AxiomAudit (1.6s)'). COMPLETE WARNING INVENTORY FOR THAT REBUILD: `grep -c warning` = 0. `grep -c error` = 0. `grep -c 'declaration uses'` = 0. `grep -ci sorry` = 0. `grep -c sorryAx` = 0. The log is 273 lines, of which 239 are `depends on axioms` lines and the ONLY non-axiom diagnostic is the pre-existing info at KyleUniqueness/Regularity.lean:57:2 ('Try this: [apply] ring_nf / The `ring` tactic failed to close the goal'). A second `lake build` immediately after is a 2 s no-op, still green.
- SORRY / UNSAFE-CONSTRUCT EVIDENCE (item 2). `grep -rn "sorry" KyleUniqueness/*.lean KyleUniqueness.lean` returns 18 hits; I printed +/-1 line of context for every one and all 18 are inside a `/-! -/` module docstring, a `/-- -/` declaration docstring, or a `--` comment: AxiomAudit 51,52,102,117; BeyondPaper 22; Main 50,180,554,562,574; Statement 20,803,872,894,1347,1372,1380,1391. ZERO executable occurrences -- consistent with the build's zero `declaration uses sorry` warnings. `grep -rnE '^ *axiom '` -> nothing. `grep -rnE 'native_decide|\bunsafe\b|\bpartial\b|\bopaque\b|@\[extern|implemented_by|\badmit\b|#exit'` -> ONE hit, Resampling.lean:862, the English word 'partial' inside a docstring ('it is a partial integral of P(Y) in L^1'). `grep -rn 'set_option'` over all project .lean files -> nothing, so no linter or check is locally suppressed. `grep -rnE 'TODO|FIXME|XXX|HACK|nolint'` -> nothing.
- AXIOM EVIDENCE (item 3). In-build: AxiomAudit.lean carries 239 `#print axioms` lines and the clean-rebuild log contains exactly 239 axiom outputs; `grep -o 'depends on axioms: \[.*\]' | sort -u` yields a set of cardinality ONE, namely `[propext, Classical.choice, Quot.sound]`. Independently, out of tree: a scratch file importing KyleUniqueness, elaborated with `lake env lean`, printing axioms for all 26 public Main.lean declarations (gamma_eq_half, KyleUniqueness.Monotone.eq_of_ae_eq_continuous, isGammaSolution_zero_iff, existsUnique_zeroSolution, the 18 KyleModel.* standardisation declarations, isEquilibrium_eq_kyleStrategy, kyle_unique_equilibrium, kyle_existsUnique_equilibrium, kyle_equilibrium_pair_iff) plus 53 further headline carriers (kyleStrategy_isEquilibrium, kyleStrategy_kylePricingRule_isEquilibrium, equilibrium_iff_zeroSolution, lemma21_flowDensity_pos/_isPricingRule/_continuous/_unique_continuous_version, lemma22_memLp_two, lemma23_integrable, jointDensity, map_value_orderFlow, gaussianSmoothing_eq_convolution, hasDerivAt_gaussianSmoothing, deriv_gaussianSmoothing, continuous_deriv_gaussianSmoothing, insiderProfit_eq_iSup, firstOrderCondition, insiderProfit_eq_sq_mul_deriv, ae_hasDerivAt_insiderProfit, insiderProfit_sub_eq_intervalIntegral, strictMono_/monotone_of_isGammaSolution, memLp_id_/memLp_strategy_posterior, deriv_inverseRegression_eq_cov/_pos, deriv_gaussianSmoothing_pos, resamplingMeasure_map_swap/_v1, integral_v1_mul_eq_inverseRegression, integral_v1_mul_comp_eq_gaussianSmoothing, one_le_sqrt_integral_sq_mul_integral_inv_sq, noiseTraderLoss_eq_integral_deriv, covariance_noise_condExp_eq_noiseTraderLoss, integral_noise_mul_sub_value_eq_noiseTraderLoss, measurable_insiderProfit, objective_eq_expectedProfit, expectedProfit_inverseRegression, integrable_noiseTraderLoss, noiseTraderLoss_le_half, noiseTraderLoss_eq_half_iff, noiseTraderLoss_eq_neg_half_iff, accounting_identity, integrable_insiderProfit_of_isGammaSolution, noiseTraderLoss_eq_integral_insiderProfit, one_le_two_mul_noiseTraderLoss, signedRoot, integral_sq_signedRoot, integral_inv_sq_rootSlope, pricingRule_ae_eq_kylePricingRule, eq_kylePricingRule_of_continuous, pricingRule_ae_orderFlow, expectedProfit_congr_ae): 79 outputs, EVERY ONE `[propext, Classical.choice, Quot.sound]`, zero sorryAx.
- LINT EVIDENCE (item 2/3 adjunct). The configured gate is `weak.linter.mathlibStandardSet := true` in lakefile.lean, which runs under `lake build` (NOT under `lake env lean` -- PROVING_LOG gotcha), so the full from-source rebuild above linted every module and produced zero `warning:` lines. Independently verified no line in any project .lean file exceeds 100 CHARACTERS (a naive byte-count awk flags 5 lines, but a UTF-8-aware pass over all 19 files finds none; those 5 lines are unicode-dense docstrings in Accounting/CondExpBridge/Regularity/SteinInequality, all files untouched by this wave).
- NON-BLOCKING, PRE-EXISTING, FOUND BY AN EXTRA CHECK NOT IN THE BRIEF: I also ran the Batteries ENVIRONMENT linter, which the lakefile does not wire up: `lake exe runLinter KyleUniqueness` -> exit 1, 'Found 1 error in 428 declarations (plus 199 automatically generated ones) in KyleUniqueness with 14 linters'. The single finding is `unusedArguments`: KyleUniqueness/GaussianHelpers.lean:202, `@KyleUniqueness.measure_prod_diagonal_eq_zero` has 1 unused argument, `argument 3: [MeasureTheory.SFinite mu]`. GaussianHelpers.lean is outside this wave's edit permissions and untouched by it (`git status` lists only KyleUniqueness.lean, AxiomAudit.lean, SignedRoot.lean, Statement.lean, Main.lean). Effect: the lemma is stated with a superfluous instance hypothesis, i.e. it is formally weaker than it needs to be. It is an internal Gaussian helper, not on the claim surface, and 13 of the 14 environment linters pass clean across all 428 declarations. Fix later by dropping the instance argument or adding `@[nolint unusedArguments]`.
- NON-BLOCKING, PRE-EXISTING: the one `info:` diagnostic in a full clean rebuild is KyleUniqueness/Regularity.lean:57:2, a `ring` -> `ring_nf` suggestion. Info level, not a warning; it does not affect exit status, warning count or axioms; the file is untouched this wave; it is PROVING_LOG gotcha #14. Same canary Stages A and B reported.
- DOC DRIFT, STILL UNFIXED AFTER STAGE B FLAGGED IT -- out of this wave's Lean edit scope but it is the ATTESTATION SURFACE and is now factually false. (a) STATEMENT_NOTES.md:12 lists the artifact as 'KyleUniqueness/Definitions.lean + KyleUniqueness/Statement.lean (+ BeyondPaper, AxiomAudit, GaussianHelpers, CondExpBridge)' -- it omits Main.lean and all six Session-3 modules. STATEMENT_NOTES.md:18-22 states 'Build status (2026-08-12 ...): 2 `sorry`s, both in Statement.lean and both headline uniqueness carriers (isGammaSolution_zero_iff rigidity direction, isEquilibrium_eq_kyleStrategy)'. Both are now proved and BOTH DECLARATIONS HAVE MOVED to KyleUniqueness/Main.lean. (b) claim-package/formalization.yaml:29 says `sorry_count: 14` (true value: 0); its `main_results` block gives `file: KyleUniqueness/Statement.lean` for kyle_equilibrium_pair_iff, kyle_unique_equilibrium, kyle_existsUnique_equilibrium and isGammaSolution_zero_iff (all now in Main.lean) with statuses 'stated (proof in progress)' / 'uniqueness half in progress'; its `alignment` block repeats 'uniqueness legs stated (sorry)', 'Proposition 2 stated (sorry x4)', 'Theorem 4 stated (sorry)', '3 regularity bridges stated (sorry)' and 'Theorem 3, Propositions 5-6, Lemmas 2.4-2.7 and the Stein inequality are deliberately NOT stated yet' -- every one of those is now false. Its scope/fidelity prose is keyed to v3 numbering throughout, while the tree's new modules are keyed to v4 (decision D1). MITIGATING: formalization.yaml line 1 reads 'DRAFT -- DO NOT POST/PUBLISH -- pending Shehral review', line 86 marks review status 'pre-publication', and SETUP.md/STATEMENT_NOTES both say 'Local only -- nothing published', so NO LIVE FALSE ATTESTATION EXISTS. It must be refreshed before any external step.
- PROCESS GAP, out of Lean scope: PROVING_LOG.md still ends at 'Session 3 -- 2026-09-16, Wave 2', with no Wave-3 entry for either Stage A (the move of the six carriers out of Statement.lean into the new top module Main.lean, the AxiomAudit rewiring, the SignedRoot rename) or Stage B (node O1, the location-scale standardisation layer). blueprint/attack_order.md's Tier-5 checklist ('AxiomAudit.lean final pass, formalization.yaml refresh, sorry count -> 0') is likewise unticked even though all three are now true of the tree. Stage B's report says its route_notes were written to be pasted verbatim; they have not been.

---

## Campaign summary — closed 2026-09-16 (working tree, uncommitted on top of commit `1570bff`)

> **Commit label.** Every figure in this section is measured on the **working
> tree of 2026-09-16**, which is uncommitted on top of commit `1570bff`. They do
> **not** hold at `1570bff` itself: there `AxiomAudit.lean` has 239 `#print axioms`
> lines, the 19 files total 9,630 lines, and `lakefile.lean` has no `lintDriver`.
> The hash must be re-pinned once the closeout is committed.

Written at the documents closeout, after the final adversarial audit returned
`pass`. This section is the campaign's own record; the claim-facing versions of
the same facts are `STATEMENT_NOTES.md` (§0 artifact, §1 crosswalk, §5 deviation
ledger, §6 what is not formalized) and `formalization.yaml`.

### Per-wave table

| Wave | Date | Nodes closed | Files produced / touched | LOC | Verification outcome |
|---|---|---|---|---:|---|
| Statement + canary phase | 2026-08-11/12 | N0, P1, A1 (positivity) | `Definitions.lean` (308), `GaussianHelpers.lean` (490), `CondExpBridge.lean` (889), `Statement.lean` (claim surface), `BeyondPaper.lean` (144), `IdentityTheoremSpike.lean` (70), `AxiomAudit.lean` | — | both definitional-fidelity canaries proved with **zero** definition changes (`CANARY_REPORT.md`); 14 tracked sorries |
| Session 1 | 2026-08-12 | N1, A2, A3, R1, Q1, Q2, `equilibrium_iff_zeroSolution`, `pricingRule_ae_eq_kylePricingRule` | `Statement.lean` in place (no new module); infra added to `GaussianHelpers`/`CondExpBridge` | — | `lake build` green; 14 sorries → **2** |
| Session 2 | 2026-08-18 | I1–I3 (*hard block 2*), R2, D1 `C¹` legs | `SteinInequality.lean` (869, **zero project imports**), `Regularity.lean` (391), `PosteriorDeriv.lean` (165) | 1,425 | green, axiom-clean; still 2 sorries (both headline carriers, gated on §4 machinery) |
| v4 re-baseline | 2026-09-16 | — (analysis) | `STATEMENT_NOTES.md` §1, `blueprint/LANE_C_DECISIONS_2026-09-16.md` | — | 10-agent workflow: 2 independent v3/v4 readers, 3 refuters, repo-impact scan, remaining-work audit + 2 refuters, W review packet. Verdict: the four headline results are unchanged up to renumbering; the §4 apparatus was rewritten; **no v3 equation number survives** |
| Session 3, Wave 1 | 2026-09-16 | B1, B2, A1b, D1-rest, D2, E1, R2b, Lemmas 3.1/3.2 | `ValueFunction.lean` (391), `Posterior.lean` (865), `Resampling.lean` (970), `Loss.lean` (283) | 2,509 | 0 sorries, axiom-clean, lint-clean; each module independently verified by an adversarial agent (rebuild from deleted oleans, out-of-tree `#print axioms`, statement-by-statement vs `paper/v4.txt`, vacuity probes at φ = id). **All four passed on the first round** |
| Session 3, Wave 2 | 2026-09-16 | E2 (*hard block 3*), H1 (*hard block 4b*), J1 | `Accounting.lean` (826), `SignedRoot.lean` (534) | 1,360 | 0 sorries, axiom-clean, lint-clean; both verified adversarially, **first round**. Hard-block census: 0 of 5 remain. E2 taken by the **full v4 route**, no fallback |
| Session 3, Wave 3 | 2026-09-16 | T3, N2, O1 | `Main.lean` (600, new top module), `AxiomAudit.lean`, `KyleUniqueness.lean`, `Statement.lean` (docstring), `SignedRoot.lean` (rename) | 600 | **from-scratch `lake build`: exit 0, 3149 jobs, 0 errors, 0 warnings, 0 `declaration uses 'sorry'`, 0 `sorryAx`.** Final audit verdict **pass**, with no repairs required in the Lean tree |
| Documents closeout | 2026-09-16 | — | `STATEMENT_NOTES.md`, `README.md`, `SETUP.md`, `claim-package/*` (5 files), `blueprint/blueprint.md`, `blueprint/attack_order.md`, three historical v3 reports, this log; **and in the Lean tree** `KyleUniqueness/AxiomAudit.lean`, `KyleUniqueness/GaussianHelpers.lean`, `KyleUniqueness/SignedRoot.lean`, `KyleUniqueness/Main.lean`, `lakefile.lean` | — | attestation surface re-keyed to v4 and to 0 sorries. Lean files **were** touched, but no statement changed: `AxiomAudit.lean` expanded from 239 to 399 `#print axioms` lines (now exhaustive) with its docstring rewritten; the unused `[SFinite μ]` instance argument dropped from `measure_prod_diagonal_eq_zero` in `GaussianHelpers.lean` (a strictly stronger lemma); two helpers renamed (`integral_insiderProfit_id'` → `integral_insiderProfit_id_of_closedForm` in `SignedRoot.lean`, `Monotone.eq_of_ae_eq_continuous` → `monotone_eq_of_ae_eq_continuous` in `Main.lean`); `lintDriver` wired into `lakefile.lean` |
| General-parameter inhabitant | 2026-09-16 | — (vacuity gap) | `KyleUniqueness/Definitions.lean` (343 → 401), `KyleUniqueness/AxiomAudit.lean` (591 → 598) | 65 | closes the last vacuity-adjacent gap: `generalModel μ₀ τ σ hτ hσ : KyleModel (ℝ × ℝ)` at arbitrary `μ₀`, `τ, σ > 0`, with `stdModel_eq_generalModel`, the parameter oracles `generalModel_priceImpact` (`λ = τ/(2σ)`) / `generalModel_kyleStrategy` (`φ(v) = (σ/τ)(v − μ₀)`) and their numeric instances at `(3, 2, 5)`. No existing statement changed. From-scratch `lake build` (project oleans deleted): exit 0, 3149 jobs, 0 errors, 0 warnings, 0 sorries; `lake lint` passes; **405** `#print axioms` lines, one distinct list |

**Totals.** 19 Lean files, **10,185 lines** by `wc -l` over
`KyleUniqueness.lean` + `KyleUniqueness/*.lean` (10,167 is the same count over
the 18 files in `KyleUniqueness/` only, excluding the 18-line root module; the
figures before the general-parameter-inhabitant wave were 10,120 / 10,102, and
the Wave-3 report's 9,630 / 9,612 are those same two counts as of commit
`1570bff`, i.e. before the documents closeout expanded `AxiomAudit.lean`). 405
`#print axioms` lines in the build, one distinct axiom list:
`[propext, Classical.choice, Quot.sound]`. Elapsed: 2026-08-11 → 2026-09-16,
of which the proving itself was three working sessions.

### The decisions that mattered

1. **D1 — re-baseline to v4 rather than finish against v3.** v4's comments field
   said "no change in theorem or proofs"; the diff said otherwise. Re-keying
   cost one analysis day and avoided shipping an artifact whose every equation
   reference was stale.
2. **D7 — keep the banked Stein inequality instead of formalizing Cacoullos.**
   `SteinInequality.lean` was already proved (Session 2, 869 LOC) and closes
   `1 ≤ 2Γ` with `f := h`. Formalizing v4's Lemma 2.7 would have re-run a hard
   block for a route change. The cost is deviation **F1**, the largest in the
   artifact, and it is disclosed everywhere.
3. **D2 — define the value function at its attained value** (`insiderProfit`),
   with `insiderProfit_eq_iSup` as the mandatory bridge. Total, junk-free, Borel
   in one line; the literal `⨆ x : ℝ` has junk value 0 exactly at H1's point `c`,
   and `EReal` is the wrong currency for every consumer. Cost: deviation **F7**.
4. **D4 — build the resampling measure explicitly on `ℝ³`** by one flat
   `withDensity`, with clauses (iii)/(iv) in bounded-test-function form, instead
   of Kallenberg transfer and `condExp`. This is what made Wave 2 tractable: the
   highest-leverage move in `Accounting.lean` was identifying μ₃'s common 2-D
   marginal with the law of `(V,Y)` on `stdModel`, which then reduced everything
   about `U⁰`/`U¹` to the second coordinate of `γ⊗γ`. Cost: deviation **F6**.
5. **D6 — take Proposition 5.1 by the v4 route, not the v3 aₙ/FOC fallback.**
   The fallback was budgeted and never needed.
6. **Wave 3 Stage A — move the six headline carriers out of `Statement.lean`
   into a new top module `Main.lean`.** Forced by the import DAG: `Statement`
   sits below every Session-3 module. The alternative (importing upward) was not
   available. Everything in `claim-package/` that names a file had to change
   because of this one move.
7. **Statement-level route for §7: standardise the laws, not the space.** Two
   Bochner integrals instead of constructing a standardised `KyleModel`. Cost:
   deviation **F12**; benefit: no second model instance to build and certify.
8. **Hypothesise `IsGammaSolution 0 φ` rather than "is an equilibrium"** in
   `gamma_eq_half` and `isGammaSolution_zero_iff` — strictly weaker, and exactly
   what the paper's own proofs reduce to in their first lines. Recorded as
   **F10**, where Lean is stronger than the paper.
9. **Take the rigidity argmax comparison at `v = 0, x = a/2`** rather than
   general `v`: `h.2 0 (a/2)` reduces to `a²/8 ≤ 0`, one specialisation cheaper
   than the paper's "the unique maximiser is `v + a/2`".
10. **Adversarial verification per module, not per campaign.** Every module was
    checked by an independent agent before the next wave consumed it; all seven
    passed on the first round, and the final audit found no Lean repairs needed.
    The defects it did find were all in the documents — which is what this
    closeout fixed.

### The twelve deviations (F1–F12)

Full text with Lean names: `STATEMENT_NOTES.md` §5;
machine-readable: `formalization.yaml`, `fidelity.deviations`.

| # | One line |
|---|---|
| F1 | v4 Lemma 2.7 (Cacoullos) has no Lean counterpart; `1 ≤ 2Γ` is proved by the **v3** one-sided Stein inequality, so for that step the formalized proof is v3's. **Largest divergence.** |
| F2 | `Γ` is *defined* as `E[U·P(Y)]` (the paper's second expression); the paper's definiens `E[U(P(Y)−V)]` and the `Cov` form are proved equal. |
| F3 | "Every Borel version" clauses (Lemma 2.3's version clause, Lemmas 3.1/3.2) are stated for the canonical `inverseRegression`; the transfer is proved machinery, never one lemma. |
| F4 | `π_y` is not formalized as a `condDistrib`; only the consequences used are proved. |
| F5 | Continuity of `P′` is not stated (differentiability, the formula and positivity are). |
| F6 | Conditional resampling is an explicit `ℝ³` measure; conditional i.i.d.-ness is not stated; (iii)/(iv) in test-function form. |
| F7 | The value function is defined at its attained value, not as a `⨆`; nonnegativity/convexity therefore carry the maximisation hypothesis. |
| F8 | `kyle_equilibrium_pair_iff` carries an explicit `Measurable P`. |
| F9 | `accounting_identity` carries a redundant `Measurable φ` alongside `Monotone φ`. |
| F10 | `gamma_eq_half` / `isGammaSolution_zero_iff` assume only `IsGammaSolution 0 φ` — **Lean is stronger**. |
| F11 | v4 Appendix B (a.e. maximisation, quasi-equilibrium) is **not formalized**; Theorem 1.1 is scoped to pointwise maximisation. |
| F12 | §7 standardises the laws, not the space; the equilibrium-transfer biconditional is never stated. |

### What is **not** formalized

1. **v4 Appendix B** — the a.e.-maximisation / quasi-equilibrium variant
   (blueprint node R3, deliberately deferred). F11.
2. **`π_y` as a version of the conditional law** (`ProbabilityTheory.condDistrib`
   appears nowhere in the tree but in two explanatory docstrings). F4.
3. **Continuity of `P′`.** F5.
4. *(This item is **closed** as of 2026-09-16 and is kept so the history reads
   straight.)* **A general-parameter `KyleModel` inhabitant.** `stdModel`
   (μ₀ = 0, τ = σ = 1) used to be the only one, so the artifact never exhibited
   Kyle's `λ = τ/(2σ)` at a value other than `1/2`. `Definitions.lean` now also
   builds `generalModel μ₀ τ σ hτ hσ : KyleModel (ℝ × ℝ)` for arbitrary `μ₀` and
   `τ, σ > 0` — the coordinates of `(gaussianReal μ₀ ⟨τ², _⟩).prod
   (gaussianReal 0 ⟨σ², _⟩)` — with `stdModel_eq_generalModel : stdModel =
   generalModel 0 1 1 one_pos one_pos`, `generalModel_priceImpact :
   λ = τ/(2σ)`, `generalModel_kyleStrategy : φ = fun v ↦ (σ/τ)(v − μ₀)` and the
   numeric oracles at `(μ₀, τ, σ) = (3, 2, 5)` (`generalModel_priceImpact_num :
   λ = 1/5`, `generalModel_kyleStrategy_num : φ = fun v ↦ 5/2 · (v − 3)`). The
   universal quantification over `M : KyleModel Ω` is therefore non-vacuous at
   every admissible parameter triple.
5. Also absent, for completeness: Cacoullos's lower Gaussian variance bound (F1),
   conditional i.i.d.-ness of the resampled pair and Kallenberg transfer (F6),
   and the §7 equilibrium-transfer biconditional (F12).

### Known non-blocking defects carried forward

Two defects that earlier waves carried are **no longer open** — they were fixed
during the documents closeout and are recorded here, past tense, so the history
reads straight:

- *(fixed)* `AxiomAudit.lean:13` used to say "every public statement is audited
  at every build" while the audit covered only part of the tree. The audit list
  was expanded at closeout and is now exhaustive — 405 of 405 public named
  declarations, independently re-derived by enumerating every column-0
  non-private named declaration across the 17 source modules (0 missing, 0
  extra; the only omissions are the four anonymous instances the docstring names).
  The docstring was rewritten to match.
- *(fixed)* `lakefile.lean` used to wire no lint driver, so `lake build` ran only
  the `mathlibStandardSet` **text** linters, and the Batteries **environment**
  linter — run by hand — reported one `unusedArguments` finding. At closeout
  `lintDriver := "batteries/runLinter"` with `lintDriverArgs := #["KyleUniqueness"]`
  was added, and the finding itself was fixed: the declaration now stands at
  `GaussianHelpers.lean:217` with `[SFinite ν]` only. `lake lint` exits 0 with
  `-- Linting passed for KyleUniqueness.` and zero findings.

**Still carried forward:**

- One info-level diagnostic in a clean rebuild: a `ring` → `ring_nf` suggestion
  at `Regularity.lean:77:2` (gotcha #14; the dated session narrative above records
  the site as line 57, which is a stale line number — 77:2 is what both of the
  closeout build logs report).
- `equilibrium_iff_zeroSolution` is now dead code by dependency — retained
  deliberately as the artifact's only single-statement rendering of the paper's
  "any Borel version" quantifier at σ = τ = 1.
- Two independent proofs of the same `φ = id` integral identity coexist
  (`integral_insiderProfit_id` in `Accounting.lean`,
  `integral_insiderProfit_id_of_closedForm` in `SignedRoot.lean`) — kept as a
  cross-check.

### Pre-publication blockers (none of them mathematics)

`claim-package/timestamp_plan.md` Phase P carries the full list; the two that
are only fixable while the repo is private: the **git-identity rewrite** of the
first three commits (`b8db757`, `86d6391`, `e842f0d`, authored as the work
identity) and **removing `claim-package/` from the repository and its history**
(currently git-tracked, while `.gitignore` carries only `/.lake` and `/paper`).
**Nothing is published; every draft still carries its `DRAFT — DO NOT
POST/PUBLISH` header.**
