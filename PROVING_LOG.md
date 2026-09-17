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
cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin/kyle-formalization
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
cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin/kyle-formalization
lake build   # green; exactly 2 "declaration uses 'sorry'" warnings
             # (Statement.lean: isGammaSolution_zero_iff,
             #  isEquilibrium_eq_kyleStrategy); AxiomAudit prints the 9
             # Stein declarations with [propext, Classical.choice, Quot.sound]
```

---

## Session 3 — 2026-09-16, Wave 1 (Fable orchestrator; opus provers + adversarial verifiers): B1, B2, A1b, D1-rest, D2, E1, R2b, Lemma 3.1/3.2 CLOSED

**Context:** arXiv v4 (2026-08-20) found to be a proof rewrite (see `V4_DELTA_REPORT_2026-09-16.md`); all Lane-C decisions delegated to the agent and recorded in `blueprint/LANE_C_DECISIONS_2026-09-16.md`. New files cite v4 numbering.

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
