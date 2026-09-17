# KyleUniqueness — Environment Setup

Lean 4 formalization of Monteiro & Tourky, "The one-period Kyle model has one
equilibrium" (arXiv:2607.23585, **v4** of 2026-08-20). Every Lean module is
keyed to v4 numbering as of the 2026-09-16 closeout wave; the v3 → v4
crosswalk is `V4_DELTA_REPORT_2026-09-16.md` §1 and the repo policy is
`blueprint/LANE_C_DECISIONS_2026-09-16.md` (decision D1). `STATEMENT_NOTES.md`
was re-keyed to v4 in the same closeout wave. Earlier reports
(`RECONCILIATION_REPORT.md`, `V3_RECONCILIATION_PLAN.md`, `CANARY_REPORT.md`)
are keyed to v3 or v2, have **not** been re-keyed, and are kept as historical
records.
Bootstrapped 2026-08-12 on macOS (Darwin 25.5.0, arm64).
**Local only — nothing here gets pushed publicly.**

## Development state (2026-09-16)

`lake build` from scratch is green: **3149 jobs, 0 errors, 0 warnings, 0
`declaration uses sorry`, 0 `sorryAx`**. 18 modules under `KyleUniqueness/`
plus the umbrella `KyleUniqueness.lean`, ~10.1k lines. `AxiomAudit.lean`
prints **399 `#print axioms` lines**, every one of them
`depends on axioms: [propext, Classical.choice, Quot.sound]` — that is every
public (non-`private`) named declaration in the tree; only the four
anonymous `instance`s cannot be cited by name.

### Module list (import order; the umbrella `KyleUniqueness.lean` lists them all)

| Module | Role | Paper (v4) |
|---|---|---|
| `Basic` | environment smoke test (`example`s only) | — |
| `Definitions` | the general model and the normalised objects | §1, §2 |
| `GaussianHelpers` | Mathlib-only Gaussian toolkit | — |
| `CondExpBridge` | density identity ⇒ `condExp` (node P1) | §1, §2.2, App. A |
| `Statement` | paper statements; `Γ` bound and equality cases | Lemmas 2.1–2.3, Prop. 4.1, Thm 1.1 (pricing half) |
| `Regularity` | `F ∈ C¹` (node R2) | Lemma 2.3, eqs. (2.2)/(2.3) |
| `PosteriorDeriv` | `C¹` legs for `p`, `n`, `P` (node D1) | Lemma 2.5 |
| `BeyondPaper` | v2's deleted quadratic-cost cubic layer | **none** (beyond-paper) |
| `IdentityTheoremSpike` | v2-endgame spike, consumer deleted in v3 | **none** |
| `SteinInequality` | one-sided Gaussian inequality (nodes I1–I3) | **v3** Lemma 2.5 — deleted in v4 (decision D7) |
| `ValueFunction` | the value function `Π = W` (nodes B1/B2) | Lemma 2.4, eqs. (2.4)–(2.6), (A.1) |
| `Posterior` | joint density, `π_y`, `P′ > 0`, `F′ > 0` | Lemma 2.1, §2.2, Lemma 2.5, eqs. (2.7)/(2.8) |
| `Resampling` | the replica measure `μ₃` (node E1) | Lemma 2.6 (i)–(iv), Lemma 2.3 tower clause |
| `Loss` | the `Γ` identities | Lemmas 3.1, 3.2 |
| `Accounting` | the accounting identity `Γ = E[Π(V)]` (node E2) | Prop. 5.1, eqs. (5.1)–(5.3) |
| `SignedRoot` | signed root `h`, `1 ≤ 2Γ` (nodes H1, J1) | inside the proof of Prop. 6.1 |
| `Main` | headline theorems | Prop. 6.1, Thm 7.1, §7, **Thm 1.1** |
| `AxiomAudit` | exhaustive `#print axioms` harness | — |

### Reproduction commands

```bash
export PATH="$HOME/.elan/bin:$PATH"     # required in EVERY shell

cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin/kyle-formalization

# 1. Full build (the verification command). Expect:
#    "Build completed successfully (3149 jobs)."
lake build

# 2. Warning / sorry / axiom inventory of that build
lake build 2>&1 | tee build.log
grep -c  "warning"            build.log    # expect 0
grep -ci "sorry"              build.log    # expect 0
grep -c  "depends on axioms"  build.log    # expect 399
grep -o  "depends on axioms: \[.*\]" build.log | sort -u
#   expect exactly one line: [propext, Classical.choice, Quot.sound]

# 3. Batteries ENVIRONMENT linters (now wired into the lakefile as well)
lake lint                       # == lake exe runLinter KyleUniqueness
#   expect "-- Linting passed for KyleUniqueness."

# 4. From-scratch rebuild of OUR modules only (leaves .lake/packages alone)
rm -rf .lake/build/lib/lean/KyleUniqueness \
       .lake/build/lib/lean/KyleUniqueness.olean \
       .lake/build/lib/lean/KyleUniqueness.ilean
lake build
```

The only non-axiom diagnostic a clean build emits is one `info:` at
`KyleUniqueness/Regularity.lean:77` (`ring` suggesting `ring_nf`). It is
info level, does not affect exit status or the warning count, and is
PROVING_LOG gotcha #14.

## Versions (pinned to match `../formal-mathfin/`)

| Component | Version |
|---|---|
| elan | 4.2.3 (b6cec7e10 2026-06-08), installed at `~/.elan` |
| Lean toolchain | `leanprover/lean4:v4.32.0` (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, arm64-apple-darwin, Release) |
| Mathlib | tag `v4.32.0` = commit `81a5d257c8e410db227a6665ed08f64fea08e997` |
| Package / library name | `KyleUniqueness` (dir `kyle-formalization/`) |

The Mathlib commit is **byte-identical to formal-mathfin's pin** (their
`lakefile.lean` requires mathlib `@ 81a5d257...`; the `math.lean` template's
`@ git "v4.32.0"` tag resolves to the same commit). All transitive deps
(batteries `023ce7d6`, aesop `a7dbf0c6`, proofwidgets `6e311e2a`, Qq, Cli,
plausible, LeanSearchClient, importGraph) also resolve to identical revisions
— the two ecosystems are olean-compatible. formal-mathfin's extra deps
(BrownianMotion, LeanArchitect, kolmogorov_extension4, subverso, checkdecls)
were deliberately NOT pulled in; add them only if a proof needs them.

## Exact commands used

```bash
# 1. elan (non-interactive, no default toolchain)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none

# 2. Pinned toolchain
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.32.0

# 3. Project (math template; toolchain forced with +)
cd /Users/shehral/quant-moonshot/problems/3-lean-mathfin
lake +leanprover/lean4:v4.32.0 new kyle-formalization math.lean
# then renamed package/lib KyleFormalization -> KyleUniqueness
# (lakefile.lean, KyleUniqueness.lean, KyleUniqueness/ dir)

# 4. Mathlib olean cache — NOT run manually: the math template's
# post-update hook ran `lake exe cache get` automatically during `lake new`.
# To re-fetch after a dep bump:
cd kyle-formalization && lake exe cache get

# 5. Build (the verification command; ~30 s warm, all-cache-hit)
lake build
```

`lake build` result at bootstrap (2026-08-12): **Build completed
successfully (3110 jobs)** — 3107 cached Mathlib modules +
`KyleUniqueness.Basic` + umbrella. Smoke tests in
`KyleUniqueness/Basic.lean`: `integral_gaussian`, `gaussianReal` as a
probability measure, conditional-expectation import. The current tree builds
**3149 jobs** (see "Development state" above).

## Cache size

- Cache download: **8639 olean files** from `lakecache.blob.core.windows.net/mathlib4-master`, ~20 min wall (network-bound, throughput swung 20 KB/s–2.4 MB/s).
- `.lake/` total: **7.6 GB** (of which `packages/mathlib/.lake` = 6.4 GB).
- `~/.elan` (toolchain v4.32.0): **2.6 GB**.

## Gotchas hit (all resolved)

1. **`Mathlib.MeasureTheory.Measure.Gaussian` does not exist** at this
   revision. Gaussian measure API lives under
   `Mathlib.Probability.Distributions.Gaussian.{Real, Basic, Multivariate,
   CharFun, Fernique, HasGaussianLaw.*, IsGaussianProcess.*}`.
   `gaussianReal m v : Measure ℝ` is the workhorse for the Kyle model's
   `v ~ N(p₀, Σ₀)`, `u ~ N(0, σᵤ²)`. `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` exists as expected.
2. **`π` notation trap**: without `open Real`, `π` in a theorem statement
   elaborates to something other than `Real.pi`, giving a bogus type
   mismatch (`√π` vs `√Real.pi`) against `integral_gaussian`. Write
   `Real.pi` explicitly (or `open Real` scoped).
3. **The math template turns on `weak.linter.mathlibStandardSet`** in
   `lakefile.lean`. Its header linter demands the exact Mathlib copyright
   block (`Copyright (c) ... All rights reserved.` / `Released under Apache
   2.0 license as described in the file LICENSE.` / `Authors: ...`) and a
   `/-! ... -/` module docstring as the first command AFTER the imports; a
   plain `/- ... -/` comment before the imports triggers a wall of warnings.
   An Apache-2.0 `LICENSE` was added so the header line is true. These are
   warnings, not errors — but keep files clean of them (formal-mathfin's
   norm is a lint-clean tree).
4. **`lake new` auto-runs `cache get`** via mathlib's post-update hook — do
   not run it a second time reflexively; the initial `lake new` call is
   therefore the long one (~20 min) and needs a generous timeout.
5. **Shell state does not persist between Bash calls** in this harness:
   `export PATH="$HOME/.elan/bin:$PATH"` (or full `~/.elan/bin/lake` paths)
   must be repeated in every invocation.
6. **Package naming**: `lake new kyle-formalization math.lean` derives the
   package/lib name `KyleFormalization` from the directory. Renaming to
   `KyleUniqueness` required editing `lakefile.lean` (`package
   "KyleUniqueness"`, `lean_lib «KyleUniqueness»`), renaming
   `KyleFormalization.lean` → `KyleUniqueness.lean` and the source dir, and
   fixing the umbrella import. No `.lake` rebuild fallout.

## Reference-repo conventions (from `../formal-mathfin/`)

**Adopted.**

- `lakefile.lean` lint gate: `lintDriver := "batteries/runLinter"` with
  `lintDriverArgs := #["KyleUniqueness"]` (advisory, scoped to our package)
  — added 2026-09-16 and verified: `lake lint` runs and passes at this pin.
- axiom-audit module (`#print axioms` harness): `KyleUniqueness/AxiomAudit.lean`,
  now exhaustive over every public named declaration (399 lines).
- `formalization.yaml` disclosure file: `claim-package/formalization.yaml`,
  refreshed at the 2026-09-16 closeout (`sorry_count: 0`, the six headline
  carriers filed under `KyleUniqueness/Main.lean`, the F1–F12 ledger inline).
  It still carries its "DRAFT — DO NOT POST/PUBLISH" header and must be
  re-verified against a fresh build before any external step.

**Still to adopt.**

- `globs := #[.andSubmodules `KyleUniqueness]` on the lean_lib so unimported
  leaf files cannot rot silently. Not needed today: the umbrella
  `KyleUniqueness.lean` imports all 18 modules explicitly, and `AxiomAudit`
  imports the two leaves (`BeyondPaper`, `IdentityTheoremSpike`) directly.
- `verification_ledger.json`. Not written yet.
- Dependency ordering rule if we ever add git deps: **mathlib require goes
  LAST** (Lake resolves transitive conflicts in favor of later requires, so
  mathlib-last keeps batteries/Cli at Mathlib's pinned revs).
