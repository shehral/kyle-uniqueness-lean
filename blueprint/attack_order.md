# Attack order — proving plan for the Kyle-uniqueness formalization (v3 revision)

> ## ⬛ CAMPAIGN COMPLETE — 2026-09-16 (working tree, uncommitted on top of
> commit `f975dbc`; figures below do not hold at that commit — re-pin the hash
> once the closeout is committed)
>
> **Every node on this DAG is closed.** Session 1 (2026-08-12) and Session 2
> (2026-08-18) cleared the early tiers and the Stein pipeline; Session 3
> (2026-09-16) ran Waves 1–3 and finished the campaign. From-scratch
> `lake build`: green, 3149 jobs, **0 `sorry`**, every audited declaration
> `[propext, Classical.choice, Quot.sound]`. 19 files, 10,185 LOC.
>
> **This document is v3-keyed and is kept as the historical proof plan.** The
> artifact is keyed to arXiv:2607.23585 **v4**; the crosswalk is
> `../STATEMENT_NOTES.md` §1 and `../V4_DELTA_REPORT_2026-09-16.md` §1, and the
> binding route decisions taken at the v4 re-baseline are
> `LANE_C_DECISIONS_2026-09-16.md` (D1–D9). Where a node name below says
> "Lemma 2.5" or "Proposition 6", read the crosswalk first.

### Node census — every node, its file, and where it was closed

| Node | Content (v3 name → v4 name) | File | Closed |
|---|---|---|---|
| N0 | model, pair predicate, `Γ`, `stdModel` | `Definitions.lean` | statement phase |
| P1 | Bayes quotient ↔ `condExp` bridge | `CondExpBridge.lean` | canary phase |
| A1 | `p` everywhere-positive density (Lemma 2.1) | `Statement.lean` | canary phase / Session 1 |
| A1b | joint density of `(V,Y)` (Lemma 2.1) | `Posterior.lean` | Session 3, Wave 1 |
| A2 | `P` continuous (Lemma 2.2) | `Statement.lean` | Session 1 |
| A3 | uniqueness of the continuous version (auxiliary) | `Statement.lean` | Session 1 |
| R1 | `P(x+U) ∈ L¹` (Lemma 2.3) | `Statement.lean` | Session 1 |
| R2 | `F ∈ C¹`, eq. (5) → **(2.3)** | `Regularity.lean` | Session 2 |
| R2b | tower clause `F(φ(V)) = E[E[V∣Y]∣V]` (Lemma 2.3) | `Resampling.lean` | Session 3, Wave 1 |
| B1 | value function: real-valued, convex, `W′ = φ` a.e. | `ValueFunction.lean` | Session 3, Wave 1 |
| B2 | FOC + strict monotonicity (Lemma 2.6 → **2.4**) | `ValueFunction.lean` | Session 3, Wave 1 |
| D1 | `P ∈ C¹`, `P′ = Cov_{π_y} > 0` (Lemma 4.1 → **2.5**) | `PosteriorDeriv.lean` (C¹ legs) + `Posterior.lean` | Session 2 + Wave 1 |
| D2 | `F′ > 0` by symmetrisation | `Posterior.lean` | Session 3, Wave 1 |
| E1 | conditional resampling (Lemma 2.4 → **2.6**) | `Resampling.lean` | Session 3, Wave 1 |
| — | `Γ = E[F′(φ(V))]`, definiens agreement (**Lemmas 3.1/3.2**, new in v4) | `Loss.lean` | Session 3, Wave 1 |
| E2 | balance/accounting identity (Prop 5 → **Prop 5.1**) — *hard block 3* | `Accounting.lean` | Session 3, Wave 2 |
| H1 | signed root (Prop 6 → unnumbered inside **Prop 6.1**) — *hard block 4b* | `SignedRoot.lean` | Session 3, Wave 2 |
| I1–I3 | one-sided Gaussian/Stein inequality (v3 Lemma 2.5) — *hard block 2* | `SteinInequality.lean` | Session 2 |
| J1 | `1 ≤ 2Γ` | `SignedRoot.lean` | Session 3, Wave 2 |
| Q1 | `\|Γ\| ≤ 1/2` (Prop 2 → **Prop 4.1**) | `Statement.lean` | Session 1 |
| Q2 | equality case `φ = ±v + a` a.e. | `Statement.lean` | Session 1 |
| N1 | affine-strategy inverse regression | `Statement.lean` | Session 1 |
| T3 | `Γ = 1/2` (Thm 3 → **Prop 6.1**) | `Main.lean` | Session 3, Wave 3 |
| N2 | rigidity `φ = id` (Thm 4 → **Thm 7.1**) | `Main.lean` | Session 3, Wave 3 |
| O1 | **Theorem 1 → 1.1**, location–scale + pair form | `Main.lean` | Session 3, Wave 3 |
| M1 | cubic / `β_γ` layer (v2 only, off-DAG) | `BeyondPaper.lean` | v2 phase, fenced |
| R3 | *optional*: a.e.-maximisation variant (v3 Lemma 2.7 → v4 **Appendix B**) | — | **NOT DONE** — deviation F11 |

Hard-block census: **0 of 5 remain.** The twelve deviations from the paper's
v4 text (F1–F12) are in `../STATEMENT_NOTES.md` §5; the one open completeness
item is a general-parameter `KyleModel` inhabitant.


**Inputs:** `blueprint.md` (v3 lemma DAG + difficulty grades),
`mathlib_api_audit.md` (verified API surface + §12 canary-phase addendum),
`../V3_RECONCILIATION_PLAN.md` (the v2 → v3 delta), `../CANARY_REPORT.md`
(what is already proved). Toolchain: Lean v4.32.0 / mathlib `81a5d257`, warm
cache, `lake build` ~30 s. Estimate horizon: **5–10 weeks** to a 0-sorry
artifact (down from v2's 6–12 — v3 deleted ~30–35 % of the planned work,
concentrated in the hardest tier).

**Local only. Nothing gets pushed or announced.**

**Already banked (canary phase + reconciliation, 2026-08-12):**
`GaussianHelpers.lean` (Tier 0.1), `CondExpBridge.lean` (node **P1 done** —
budgeted for Tier 3 in the v2 plan), both canaries proved
(`kyleStrategy_isEquilibrium`, `lemma21_isPricingRule`),
`lemma21_flowDensity_pos`, `isPricingRule_kylePricingRule`, the pair-form
existence `kyleStrategy_kylePricingRule_isEquilibrium`, the
version-independence glue (`pricingRule_ae_orderFlow`,
`expectedProfit_congr_ae`), the beyond-paper cubic layer (v2 Tier 0.2,
now fenced in `BeyondPaper.lean`), and the identity-theorem spike (v2 Tier
0.4 — its consumer was deleted by v3; retained as infrastructure).

**Session-1 update (2026-08-12, `../PROVING_LOG.md`): ALL of Tier 1 is
closed** (N1, A2, A3, sorry #14, Q1 ×3), plus **R1** (Tier-2 front α,
`lemma23_integrable`), the **`σ=τ=1` bridge** (`equilibrium_iff_zeroSolution`)
and **Q2 in full** (`noiseTraderLoss_eq_half_iff` both signs — the node
that replaced v2 hard blocks 4a/5). New banked infrastructure: the
order-flow law identity `KyleModel.map_orderFlow`, the `K_x`
complete-the-square kernel toolkit, and the L² identity behind Prop 2.
Milestones M1, M3's demo checkpoint, M2's #14-half and M4's Q2-half are
hit ahead of schedule. **2 sorries remain** — the two headline carriers
(N2's rigidity direction; O1's strategy half) — gated exactly on the
remaining critical path: I1–I3 (front β, unstarted), R2, B1/B2, D1/D2,
E1/**E2**, **H1**, J1, T3.

---

## 1. Resource model (three lanes — unchanged)

| Lane | What it is | Best at | Throughput assumption |
|---|---|---|---|
| **Lane A — frontier-model agents** (Claude-Code sessions against the local REPL loop) | interactive sessions with full blueprint context, grep-of-pin verification, `lake build` feedback | mechanical + standard nodes with a written skeleton; API archaeology; side-goal grinding | 2–4 blueprint leaf-goals / session; parallelizable across files that don't share imports |
| **Lane B — open-weight prover loop on H200s** (Explorer cluster; propose-verify against `sorry`-holed goal files) | high-volume tactic search on closed, self-contained goals | algebra/inequality leaves (Q1's L² algebra, N1's complete-the-square, R1's exp-identities); retry-farms on stuck leaves | 50–200 goal attempts/night; ~10–30 % close rate on well-posed leaves |
| **Lane C — human+AI co-work** (Shehral + frontier agent, synchronous) | design authority | statement review of proof-internal defs (`W`, `π_y`, μ₃), the a.e. skeletons of the hard blocks (E2, H1), unblocking Lane A | ≤ 2 focused blocks/week |
|

**Routing rule** (unchanged): every node starts as a Lane-C *statement
review*, Lane A drafts the skeleton with `sorry` leaves, surviving leaves go
to Lane B overnight; two failures bounce a goal up a lane. Hard blocks
invert: Lane C writes the skeleton first.

**Verification gate** (in force since day 1): `lake build` green at every
merge; `AxiomAudit.lean` per-declaration `#print axioms` at every build; no
new `sorry` outside the tracked inventory.

---

## 2. Tiered attack list (v3)

### Tier 1 — cheap wins off the banked infrastructure (Lane A, start immediately; Lane B farms leaves)

| Order | Node / sorry | Why now |
|---|---|---|
| 1.1 | **N1** (`inverseRegression_affine`, `gaussianSmoothing_affine`) | the canary phase already proved the Kyle-shaped complete-the-square and the translation toolkit; ~100–200 LOC of `GaussianHelpers`-driven algebra; unblocks Q2 and N2 |
| 1.2 | **A2** (`lemma21_continuous`) + A1's remaining marginal/continuity clauses | mechanical DCT; same file as the proved positivity |
| 1.3 | **pricing half** (`pricingRule_ae_eq_kylePricingRule`, sorry #14) | low-medium: flow-a.s. → Lebesgue-a.e. via `flowPDF_kyleStrategy`'s explicit `N(0, 2σ²)` density (proved) + withDensity null-set transfer; closes the last sorried leg of `eq_kylePricingRule_of_continuous` |
| 1.4 | **Q1** (`lemma22_memLp_two`, `integrable_noiseTraderLoss`, `noiseTraderLoss_le_half`) | elementary L² algebra over P1's master identity (done); the paper's pivot bound; `nlinarith` food for Lane B |
| 1.5 | **A3** (`lemma21_unique_continuous_version`) | 5 lines of topology; auxiliary but cheap |

### Tier 2 — the new regularity spine (Lane A ×2 in parallel; replaces v2's A4/A5 slog)

- **Front α:** **R1** (`lemma23_integrable`, the K_x kernel bound) then
  **R2** (`F ∈ C¹` + eq. (5)) in `Regularity.lean`. Standard grade; the
  ℝ-only `hasDerivAt_integral_of_dominated_loc_of_deriv_le` instantiation
  replaces the entire v2 complex-analytic layer.
- **Front β:** **I1 → I2 → I3** in `SteinInequality.lean` (zero project
  imports — pure Mathlib; v3 Lemma 2.5 unchanged from v2). Front-load it:
  premier upstream artifact, and if the audit's de-fanging is wrong we find
  out in week 2, not week 7.

### Tier 3 — value function + posterior (Lane A after R2)

- **B1 → B2** (`ValueFunction.lean`; Lemma 2.6 at γ = 0; W in attainment
  form, FOC, strict monotonicity).
- **D1 → D2** (`PosteriorDeriv.lean`; P ∈ C¹, P′ = Cov > 0; F′ > 0 by v3's
  symmetrisation — no IBP).
- **Q2** (`noiseTraderLoss_eq_half_iff`, `noiseTraderLoss_eq_neg_half_iff`)
  once Q1 + N1 exist: the Tonelli-sections + translation-invariance
  rigidity. Lane C reviews the a.e.-bookkeeping skeleton once; Lane A
  fills. **This is the node that replaced v2 hard blocks 4a and 5 — treat
  its skeleton with hard-block care even though every ingredient is
  standard.**

### Tier 4 — the probabilistic engine (Lane C + A; the schedule risk)

- **E1** (μ₃ / conditional resampling, Lemma 2.4 (i)–(iv)) — Lane A from a
  Lane-C-approved definition.
- **E2** (Prop 5 balance identity Γ = E[F′(φV)] = E[W(V)]) — **hard block
  3, the highest-variance node** (reduced by v3: one fewer leg, one fewer
  MCT pass). Lane C owns the chain skeleton and the ℝ≥0∞-vs-Bochner
  strategy.
- **H1** (Prop 6 signed root) — **hard block 4b**, Lane C skeleton (the
  `c`-point case analysis and a.e. set management), Lane A/B fill ~15
  leaves.
- **J1** (1 ≤ 2Γ; one Stein application) and **T3** (Γ = 1/2 assembly) —
  mechanical glue, hours.

### Tier 5 — rigidity endgame + headline (Lane A with Lane C on call)

- [x] **N2** (v3 Theorem 4 = v4 **Theorem 7.1** = `isGammaSolution_zero_iff`):
  T3 + Q2 + N1 + the quadratic-argmax comparison forcing `a = 0`.
  **CLOSED** 2026-09-16 (Wave 3 Stage A) in `KyleUniqueness/Main.lean`, with
  the helper `monotone_eq_of_ae_eq_continuous`.
- [x] **equilibrium_iff_zeroSolution** (the σ = τ = 1 bridge; Fubini +
  `expectedProfit_congr_ae`) — **CLOSED** in Session 1, `Statement.lean`.
  Note its role changed: the Wave-3 headline route reaches Theorem 1.1 via
  `pricingRule_ae_eq_of_flowPDF_pos` + `expectedProfit_congr_ae` +
  `expectedProfit_bayesPrice` and never calls it. It is retained as the
  artifact's only single-statement rendering of the paper's "any Borel
  version" quantifier at σ = τ = 1 — a faithfulness certificate, not a
  load-bearing lemma.
- [x] **O1** (`isEquilibrium_eq_kyleStrategy` via location–scale; the pair-iff
  assembled) — **CLOSED** 2026-09-16 (Wave 3 Stage B) in `Main.lean`, by
  standardising the **laws** rather than the probability space (deviation
  F12). The final faithfulness review was done against **v4** §1 by an
  independent adversarial auditor; its ledger is `STATEMENT_NOTES.md` §5.
- [x] `AxiomAudit.lean` final pass — **DONE** (Wave 3 + closeout: 399 `#print
  axioms` lines, exhaustive over every public named declaration; single
  distinct axiom list `[propext, Classical.choice, Quot.sound]`). Raised to 405
  lines on 2026-09-16 by the six `generalModel` declarations.
- [x] sorry count → 0 — **DONE** 2026-09-16, commit `f975dbc`; from-scratch
  `lake build` green, 3149 jobs, zero `declaration uses 'sorry'`.
- [x] `formalization.yaml` refresh — **DONE** in the documents closeout
  (2026-09-16), together with `STATEMENT_NOTES.md`, `README_draft.md`, the
  repo-root `README.md`, and the three publication drafts.
- [ ] **Optional post-headline (R3): NOT DONE — deliberately out of scope.**
  v3's Lemma 2.7 became v4 **Appendix B** (a different statement: a.e.
  maximisation / quasi-equilibrium). Not formalized; recorded as deviation
  **F11**. Theorem 1.1 is therefore scoped to the *pointwise*-maximisation
  definition.
- [x] Not a blueprint node, but the one open completeness item found by the
  closing audit: **a general-parameter `KyleModel` inhabitant** — **CLOSED**
  2026-09-16. `Definitions.lean` now carries `generalModel μ₀ τ σ hτ hσ :
  KyleModel (ℝ × ℝ)` for arbitrary `μ₀` and `τ, σ > 0`, with
  `stdModel_eq_generalModel`, `generalModel_priceImpact` (`λ = τ/(2σ)`),
  `generalModel_kyleStrategy` (`φ(v) = (σ/τ)(v − μ₀)`) and numeric oracles at
  `(μ₀, τ, σ) = (3, 2, 5)`; all six audited.

---

## 3. Week-by-week Gantt (6-week nominal, 5-week floor / 10-week ceiling)

```
Week  Lane A1 (stream 1)            Lane A2 (stream 2)            Lane B (overnight)        Lane C (Shehral blocks)
────  ────────────────────────────  ────────────────────────────  ────────────────────────  ─────────────────────────
 1    T1.1 N1 affine regression;    I1 Stein IBP (layer-cake)     Q1 L² algebra farm;       W/π_y/μ₃ statement review;
      T1.2 A2 continuity; T1.5 A3                                 N1 complete-square         Q2 skeleton design
 2    T1.3 pricing half (#14);      I2 domination + I3 assembly   R1 exp-identity farm      R1 K_x statement review;
      T1.4 Q1 (uses P1, done)       (hard block 2 CLOSES wk 2)                              E2 chain skeleton (2 blocks)
 3    R1 K_x kernel bound           B1 ValueFunction (vs opaque   R1/R2 side-goals;         H1 skeleton design
                                    F-hypothesis from R2 stmt)    B1 leaves
 4    R2 F in C1 + eq (5)           B2 FOC; D1 posterior C1       D1 Integrable farm        Q2 review (equality case);
                                                                                            E2 link-by-link review
 5    Q2 equality case ◄━━ NEW      D2 symmetrisation; E1         E2 per-link side-goals    E2 + H1 unblocking
      MATH (but standard grade)     construction                                            (2 blocks)
 6    E2 balance chain ◄━━ RISK     H1 SignedRoot fill            H1 leaves (~15);          final statement review
      J1+T3 glue; N2 Theorem 4      equilibrium_iff_zeroSolution  N2 argmax leaves          vs v3 §1 (faithfulness
      O1 location-scale + headline  + O1 plumbing                                           ledger); sign-off
────  ────────────────────────────  ────────────────────────────  ────────────────────────  ─────────────────────────
 7-8  SLACK: absorbs E2 overrun (most likely), H1 overrun (second), Q2 surprises, statement-cascade repairs.
 9-10 SLACK: second hard-block overrun; else upstream-package polish (I1–I3, Stein minis, CondExpBridge,
      GaussianHelpers) + internal writeup. Ship 0-sorry artifact no later than end of week 10.
```

**Critical path (v3):** A2 → R1 → R2 → B1/B2 → D1 → D2 → E1 → **E2** →
**H1** → **I1–I3** → J1 → T3 (with Q1) → **Q2** → N2 → O1.
Weeks 3–6 are the exposure window. The Stein file and H1 remain the two
ex-ante scariest blocks and both get finished or falsified by week 6.
Everything on Tier 1 has float and doubles as Lane-B pilot food.

**Milestones / kill-switches:**
- **M1 (end wk 1):** N1 + A2 + ≥ 1 Q1 leg on main; Lane B closing Q1/N1
  leaves. If Lane B's harness still isn't closing leaves by wk 2, drop
  Lane B and re-plan A-only (costs ~1 week).
- **M2 (end wk 2):** Stein file 0-sorry (hard block 2 dead — one week
  earlier than the v2 plan) and sorry #14 closed (pricing half done ⇒
  `eq_kylePricingRule_of_continuous` fully kernel-checked).
- **M3 (end wk 4):** Prop 2 bounds (Q1) fully closed and R2 landed —
  `noiseTraderLoss_le_half` proved is the natural internal demo checkpoint
  (the paper's pivot inequality, machine-checked).
- **M4 (end wk 5–6):** Q2 closed (the rigidity equality) and E2 closed.
  Remaining work is assembly-grade.
- **M5 (end wk 6–10):** `kyle_equilibrium_pair_iff` 0-sorry through all
  legs, axiom-clean, faithfulness ledger checked. **Then stop.** Review
  with the user before ANY external step — Zulip search, arXiv re-check
  (v4?), upstream PRs, author contact are all user decisions, not this
  plan's.

**Standing rules for all lanes** (from SETUP.md gotchas + audit §11–12 +
CANARY_REPORT toolchain notes): `export PATH="$HOME/.elan/bin:$PATH"` in
every shell; verify every proposed lemma name by grep-of-pin (never
loogle/memory — and remember the pin's atoms API is `NullSingletonClass`,
not `NoAtoms`); `Real.pi` explicitly or `open Real`; `gaussianPDFReal_eval`
before any pdf-lemma rewrite (NNReal anonymous constructors are
simp-opaque); bind measurability proofs to explicit-lambda `have`s before
`rw`-ing integral lemmas; keep files lint-clean against
`mathlibStandardSet`; mathlib-require-last if any dep is ever added.
