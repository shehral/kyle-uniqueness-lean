/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Definitions

/-!
# Beyond-paper: the cubic-root layer of the quadratic-cost family

**BEYOND-PAPER MATERIAL — read this header before citing anything below.**

This file formalizes the root layer of the quadratic-trading-cost
generalisation that appeared in **v2** of Monteiro & Tourky
(arXiv:2607.23585v2, Definition 2.2 / Theorem 3.2 / Remark 5.4: `γ`-solutions
with objective `x(v − F(x)) − (γ/2)x²`, classified as `φ = β_γ · id` with
`β_γ` the unique positive root of the cubic `γt³ + t² + γt = 1`) and was
**deleted from the paper in v3** (2026-08-10). No published version of the
paper now states these results; v3 keeps only the frictionless `γ = 0`
instance (its condition (17) and Theorem 4).

We keep the layer because it is **fully proved** (no `sorry`, axioms
`propext, Classical.choice, Quot.sound` only) and correct mathematics: the
existence, uniqueness and bounds for the positive root of the cubic, by the
intermediate value theorem and strict monotonicity. It is offered as **our
own extension** of the formalization, anchored to v2's deleted material, not
as formalized content of arXiv:2607.23585v3. Claim-package documents must
label anything from this file accordingly.

The only facts from this layer that remain load-bearing for the v3-facing
statements are the trivial specialisations `betaGamma_zero : betaGamma 0 = 1`
and `lambdaGamma 0 = 1/2` (matching `λ = τ/(2σ)` of v3 eq. (2) at
`τ = σ = 1`) — and the v3 statements in `KyleUniqueness.Statement` do not
import them; they are restated there in closed form.
-/

open MeasureTheory ProbabilityTheory

namespace KyleUniqueness

/-! ## The cubic `γt³ + t² + γt = 1` (v2 Theorem 3.2, deleted in v3)

v2's Theorem 3.2 characterised the unique `γ`-solution as `φ(v) = β_γ v`
with `β_γ ∈ (0, 1]` "the unique positive root of `γt³ + t² + γt = 1`". The
root's existence and uniqueness are elementary (IVT plus strict
monotonicity — v2's own argument) and are proved here outright, so that the
slope `betaGamma` below is a genuine definition rather than an axiom. -/

/-- The cubic `t ↦ γt³ + t² + γt` is strictly increasing on `(0, ∞)` for
`γ ≥ 0` (v2 proof of Theorem 3.2: "its derivative `3γt² + 2t + γ` is
positive for every `t > 0`"; we argue directly, without derivatives). -/
theorem cubic_strictMonoOn (γ : ℝ) (hγ : 0 ≤ γ) :
    StrictMonoOn (fun t : ℝ => γ * t ^ 3 + t ^ 2 + γ * t) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h3 : a ^ 3 < b ^ 3 := by
    nlinarith [mul_pos (sub_pos.mpr hab)
      (add_pos (add_pos (pow_pos hb' 2) (mul_pos ha' hb')) (pow_pos ha' 2))]
  have h2 : a ^ 2 < b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) (add_pos hb' ha')]
  have hγ3 := mul_le_mul_of_nonneg_left h3.le hγ
  have hγ1 := mul_le_mul_of_nonneg_left hab.le hγ
  change γ * a ^ 3 + a ^ 2 + γ * a < γ * b ^ 3 + b ^ 2 + γ * b
  linarith

/-- For every `γ ≥ 0` the cubic `γt³ + t² + γt = 1` has a unique positive
root (v2 proof of Theorem 3.2: values `−1` at `0` and `2γ ≥ 0` at `1`, IVT,
strict monotonicity). -/
theorem cubic_pos_root_existsUnique (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃! t : ℝ, 0 < t ∧ γ * t ^ 3 + t ^ 2 + γ * t = 1 := by
  obtain ⟨t, ht01, htval⟩ :
      ∃ t ∈ Set.Icc (0 : ℝ) 1, γ * t ^ 3 + t ^ 2 + γ * t = 1 := by
    have hcont : ContinuousOn (fun t : ℝ => γ * t ^ 3 + t ^ 2 + γ * t)
        (Set.Icc 0 1) := (by fun_prop : Continuous _).continuousOn
    have hmem : (1 : ℝ) ∈
        Set.Icc (γ * 0 ^ 3 + 0 ^ 2 + γ * 0) (γ * 1 ^ 3 + 1 ^ 2 + γ * 1) := by
      rw [Set.mem_Icc]
      constructor <;> nlinarith
    exact intermediate_value_Icc zero_le_one hcont hmem
  have htpos : 0 < t := by
    rcases ht01.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at htval; norm_num at htval
  refine ⟨t, ⟨htpos, htval⟩, ?_⟩
  rintro s ⟨hs, hsval⟩
  refine (cubic_strictMonoOn γ hγ).injOn (Set.mem_Ioi.mpr hs)
    (Set.mem_Ioi.mpr htpos) ?_
  rw [hsval, htval]

/-- The equilibrium slope `β_γ`: the unique positive root of
`γt³ + t² + γt = 1` (v2 Theorem 3.2). Junk value `1` for `γ < 0` (where
v2's Remark 5.4 — also deleted in v3 — showed the root is genuinely
non-unique). -/
noncomputable def betaGamma (γ : ℝ) : ℝ :=
  if hγ : 0 ≤ γ then (cubic_pos_root_existsUnique γ hγ).exists.choose else 1

/-- `β_γ` is positive (v2 Theorem 3.2). -/
theorem betaGamma_pos {γ : ℝ} (hγ : 0 ≤ γ) : 0 < betaGamma γ := by
  rw [betaGamma, dif_pos hγ]
  exact (cubic_pos_root_existsUnique γ hγ).exists.choose_spec.1

/-- `β_γ` is a root of the cubic of v2 Theorem 3.2. -/
theorem betaGamma_root {γ : ℝ} (hγ : 0 ≤ γ) :
    γ * betaGamma γ ^ 3 + betaGamma γ ^ 2 + γ * betaGamma γ = 1 := by
  rw [betaGamma, dif_pos hγ]
  exact (cubic_pos_root_existsUnique γ hγ).exists.choose_spec.2

/-- Any positive root of the cubic equals `β_γ` (uniqueness half of
v2 Theorem 3.2's root claim). -/
theorem betaGamma_unique {γ : ℝ} (hγ : 0 ≤ γ) {t : ℝ} (ht : 0 < t)
    (h : γ * t ^ 3 + t ^ 2 + γ * t = 1) : t = betaGamma γ :=
  (cubic_pos_root_existsUnique γ hγ).unique ⟨ht, h⟩
    ⟨betaGamma_pos hγ, betaGamma_root hγ⟩

/-- `β₀ = 1`: at `γ = 0` the cubic reduces to `t² = 1` on `(0, ∞)`. This
specialisation is the point of contact with v3: it recovers the identity
strategy of v3 Theorem 4. -/
theorem betaGamma_zero : betaGamma 0 = 1 :=
  (betaGamma_unique le_rfl one_pos (by norm_num)).symm

/-- `β_γ ≤ 1` — i.e. `β_γ ∈ (0, 1]` as asserted in v2 Theorem 3.2. -/
theorem betaGamma_le_one {γ : ℝ} (hγ : 0 ≤ γ) : betaGamma γ ≤ 1 := by
  by_contra h
  have hlt := cubic_strictMonoOn γ hγ (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (betaGamma_pos hγ)) (not_le.mp h)
  have hlt' : γ * 1 ^ 3 + 1 ^ 2 + γ * 1 <
      γ * betaGamma γ ^ 3 + betaGamma γ ^ 2 + γ * betaGamma γ := hlt
  have hroot := betaGamma_root hγ
  nlinarith

/-- The normalised price impact `λ_γ = β_γ / (1 + β_γ²)` (v2 Theorem 3.2:
in the unique `γ`-solution, `P(y) = λ_γ y` and `F(x) = λ_γ x`). At `γ = 0`
this is `1/2`, matching `λ = τ/(2σ)` of v3 eq. (2) at `τ = σ = 1`. -/
noncomputable def lambdaGamma (γ : ℝ) : ℝ :=
  betaGamma γ / (1 + betaGamma γ ^ 2)

/-- Sanity for the `γ = 0` contact point: `λ₀ = 1/2` (v3 eq. (2) at
`τ = σ = 1`). -/
theorem lambdaGamma_zero : lambdaGamma 0 = 1 / 2 := by
  rw [lambdaGamma, betaGamma_zero]
  norm_num

end KyleUniqueness
