import Lake
open Lake DSL

package "KyleUniqueness" where
  version := v!"0.1.0"
  keywords := #["math"]
  -- Batteries ENVIRONMENT linters, scoped to our package (advisory).
  -- `lake build` only runs the mathlibStandardSet TEXT linters; this wires
  -- `lake lint` to the same check as `lake exe runLinter KyleUniqueness`.
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["KyleUniqueness"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.32.0"

@[default_target]
lean_lib «KyleUniqueness» where
  -- add any library configuration options here
