# KyleUniqueness — Environment Setup

Lean 4 formalization of Monteiro & Tourky, "The one-period Gaussian Kyle
model has exactly one equilibrium" (arXiv:2607.23585; statements track v3 —
see `RECONCILIATION_REPORT.md`). Bootstrapped 2026-08-12 on macOS
(Darwin 25.5.0, arm64). **Local only — nothing here gets pushed publicly.**

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

`lake build` result: **Build completed successfully (3110 jobs)** —
3107 cached Mathlib modules + `KyleUniqueness.Basic` + umbrella. Smoke tests
in `KyleUniqueness/Basic.lean`: `integral_gaussian`, `gaussianReal` as a
probability measure, conditional-expectation import.

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

## Reference-repo conventions to adopt later (from `../formal-mathfin/`)

- `lakefile.lean` lint gate: `lintDriver := "batteries/runLinter"` with
  `lintDriverArgs := #["KyleUniqueness"]` (advisory, scoped to our package).
- `globs := #[.andSubmodules `KyleUniqueness]` on the lean_lib so unimported
  leaf files (axiom-audit harness, examples) cannot rot silently.
- `formalization.yaml` disclosure file + `verification_ledger.json` +
  axiom-audit module (`#print axioms` harness) — to be created in the
  statement/blueprint phase.
- Dependency ordering rule if we ever add git deps: **mathlib require goes
  LAST** (Lake resolves transitive conflicts in favor of later requires, so
  mathlib-last keeps batteries/Cli at Mathlib's pinned revs).
