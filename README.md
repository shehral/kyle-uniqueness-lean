# KyleUniqueness — the one-period Kyle model, formalized in Lean 4

A Lean 4 / Mathlib formalization of Monteiro & Tourky, *"The one-period Kyle
model has one equilibrium"* (arXiv:2607.23585v4). The paper settles a question
open since Kyle (1985): in the one-period Gaussian Kyle model of insider
trading, the equilibrium pair (insider strategy, pricing rule) is **unique
among all Borel strategies**, with no regularity or moment assumptions. This
repository contains the machine-checked statements and proofs: the model, the
equilibrium pair predicate, the noise-traders'-loss pivot `Γ`, and the headline
characterisation `kyle_equilibrium_pair_iff`, together with the regularity,
resampling, accounting and signed-root machinery the proof needs. It depends on
Mathlib alone — one period means no stochastic calculus.

## Status

**Complete. 0 `sorry`, axiom-clean — as of the working tree of 2026-09-16, uncommitted on top of commit `f975dbc` (the hash must be re-pinned once the closeout is committed).**

- From-scratch `lake build`: green, 3149 jobs, zero errors, zero warnings, zero
  `declaration uses 'sorry'`.
- 19 Lean files, 10,120 lines.
- Every audited declaration depends only on `[propext, Classical.choice,
  Quot.sound]` — no `sorryAx`, no project-local axiom, no `native_decide`, no
  `unsafe`/`partial`/`opaque`/`@[extern]`/`@[implemented_by]`.
- Headline theorems live in `KyleUniqueness/Main.lean`:
  `kyle_equilibrium_pair_iff` (v4 Theorem 1.1), `kyle_unique_equilibrium`,
  `kyle_existsUnique_equilibrium`, `isEquilibrium_eq_kyleStrategy`,
  `isGammaSolution_zero_iff` (v4 Theorem 7.1), `existsUnique_zeroSolution`,
  `gamma_eq_half` (v4 Proposition 6.1).

Deviations from the paper's text (twelve of them, all deliberate or
wording-level, none affecting a headline claim) are itemised as **F1–F12** in
[`STATEMENT_NOTES.md`](STATEMENT_NOTES.md) §5. The most important: for the step
`1 ≤ 2Γ` inside v4 Proposition 6.1 the formalized proof follows v3's one-sided
Stein inequality, not v4's Cacoullos bound (F1); v4 Appendix B is not
formalized (F11).

## Paper

> P. K. Monteiro, R. Tourky. *The one-period Kyle model has one equilibrium.*
> arXiv:2607.23585v4, 2026-08-20.

Numbering throughout the Lean tree and the current documents is **v4's**.
Earlier versions carried different titles and numbering (v3, 2026-08-10, *"The
one-period Gaussian Kyle model has exactly one equilibrium"*; v2, *"Monotonicity
and Rigidity in Gaussian Inverse Regression — The One-Period Kyle Model Has a
Unique Equilibrium"*). The v3 → v4 crosswalk is in
[`STATEMENT_NOTES.md`](STATEMENT_NOTES.md) §1 and, at full length, in
[`V4_DELTA_REPORT_2026-09-16.md`](V4_DELTA_REPORT_2026-09-16.md) §1.

## Build

Toolchain pin: Lean `leanprover/lean4:v4.32.0`, Mathlib `81a5d257` (tag
v4.32.0). `elan` installs the pin automatically from `lean-toolchain`.

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get     # Mathlib olean cache
lake build             # the verification — green, 0 sorries
```

The axiom audit runs as part of the build: `KyleUniqueness/AxiomAudit.lean`
emits 399 `#print axioms` lines, each of which must read
`[propext, Classical.choice, Quot.sound]`.

```bash
lake build 2>&1 | grep -o "depends on axioms: \[.*\]" | sort -u   # expect one line
```

Setup details and environment gotchas: [`SETUP.md`](SETUP.md).

## Map of the repository

| Path | What it is |
|---|---|
| `KyleUniqueness/` | the Lean development (18 modules, plus the umbrella `KyleUniqueness.lean` at the repo root — see `STATEMENT_NOTES.md` §0) |
| `STATEMENT_NOTES.md` | paper-object → Lean-object map, v3↔v4 crosswalk, the F1–F12 deviation ledger |
| `PROVING_LOG.md` | the proving campaign, session by session, with the closing campaign summary |
| `blueprint/` | the lemma DAG, attack order, and the Mathlib API audit (campaign complete) |
| `V4_DELTA_REPORT_2026-09-16.md` | the v3 → v4 reconciliation |
| `claim-package/` | **private** publication drafts — not for publication as-is |

## Publication status

**Nothing here is published.** `claim-package/README_draft.md` is the draft of
the public README, `claim-package/formalization.yaml` the machine-readable
AI-assistance and faithfulness disclosure, and
`claim-package/timestamp_plan.md` the (unexecuted) release plan. All three
carry `DRAFT — DO NOT POST/PUBLISH` headers and unresolved `<REPO-URL>` /
`<DOI>` placeholders, and `claim-package/` must be removed from the repository
and its history before any public flip.

## License

Apache-2.0 (see [`LICENSE`](LICENSE)). The mathematics is Monteiro & Tourky's;
this repository is the formalization of it.
