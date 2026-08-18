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
