/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.ValueFunction
import KyleUniqueness.Posterior
import KyleUniqueness.Loss
import KyleUniqueness.SteinInequality

/-!
# The signed root `h` and the bound `1 ≤ 2Γ` (blueprint nodes H1 and J1)

Formalization of the construction inside the proof of **Proposition 6.1** of
Monteiro & Tourky, *The one-period Kyle model has one
equilibrium* (arXiv:2607.23585, **v4** of 2026-08-20; the construction is
v3's Proposition 6), together with the resulting inequality `Γ ≥ 1/2`.

## Contents

Throughout, `γ := gaussianReal 0 1` is the law of the asset value,
`F := gaussianSmoothing φ`, `W := insiderProfit φ` (v4's `Π = W`, node B1)
and `Γ := noiseTraderLoss φ`, all under the standing hypothesis
`h : IsGammaSolution 0 φ` (the paper's pointwise maximisation condition).

* `criticalPoint φ = F(0)` — the paper's `c`; `strategy_criticalPoint`
  is `φ(c) = 0`, with the two sign clauses
  `strategy_neg_of_lt_criticalPoint` and `strategy_pos_of_criticalPoint_lt`;
* `posteriorSlope φ v = F′(φ(v))` — the paper's `q`, positive everywhere
  (v4 Lemma 2.5 eq. (2.8)), Borel, `γ`-integrable, with
  `noiseTraderLoss_eq_integral_posteriorSlope` (`Γ = E[q(V)]`, v4 Lemma 3.1)
  and hence `noiseTraderLoss_pos` (`Γ > 0`);
* `insiderProfit_criticalPoint` (`W(c) = 0`) and `insiderProfit_pos_of_ne`
  (`W > 0` off `c`), from `W = φ²q`;
* `signedRoot φ` — the paper's `h = sign(· − c)·√(2W)` — and `rootSlope φ` —
  the paper's `r = 1/√(2q)`; the pointwise dictionary `signedRoot_sq`
  (`h² = 2W`) and `inv_rootSlope_sq` (`1/r² = 2q`);
* `continuous_signedRoot`, `strictMono_signedRoot` and
  `ae_hasDerivAt_signedRoot` (`h′ = r` Lebesgue-a.e.) — the analytic content
  of the construction;
* the moment identities `integrable_sq_signedRoot_iff`,
  `integral_sq_signedRoot` (`E[h(V)²] = 2E[W(V)]`),
  `integrable_inv_sq_rootSlope` and `integral_inv_sq_rootSlope`
  (`E[1/r(V)²] = 2Γ`);
* **J1**: `one_le_two_mul_noiseTraderLoss`, the half of v4 Proposition 6.1
  that reads `1 ≤ 2Γ`;
* the sanity oracles at `φ = id` (`criticalPoint_id`, `posteriorSlope_id`,
  `signedRoot_id`, `rootSlope_id`, `two_mul_noiseTraderLoss_id`), which also
  show the J1 bound is attained, hence non-vacuous.

## Route, and the one deviation from v4 (Lane-C decision D7)

Everything through the moment identities follows v4's construction verbatim.
The final step does **not**: v4 derives `Γ ≥ 1/2` from its Lemma 2.7
(Cacoullos, `(E[f′(V)])² ≤ Var f(V)`) through a truncation-plus-Cauchy–
Schwarz argument, whereas we feed the banked one-sided Stein inequality
`one_le_sqrt_integral_sq_mul_integral_inv_sq`
(`KyleUniqueness.SteinInequality`, blueprint nodes I1–I3 = v3's Lemma 2.5,
deleted in v4) the pair `(h, r)` directly. The two routes prove the same
inequality from the same two moments; ours needs no truncation sequence and
no `L²` convergence argument.

Two further presentational deviations, both proof-shortening:

* v4 proves local absolute continuity of `h` by a Lipschitz estimate on
  compacts through `c`. We never need absolute continuity of `h` as such:
  the Stein inequality consumes exactly `Monotone h` plus the a.e. derivative
  identity, so we prove `StrictMono` (from the sign of `φ` and strict
  monotonicity of `W` on each side of `c`, both consequences of the
  subgradient inequality (A.1)) and the a.e. `HasDerivAt` (chain rule through
  `Real.sqrt` at every `v ≠ c` at which `φ` is continuous — a co-countable
  set). Continuity of `h`, which we also prove, is then a bonus.
* the paper's `2W(J) ⊂ (0,∞)` compactness argument is replaced by the
  pointwise statement `W(v) > 0` for `v ≠ c`, which is all the chain rule
  needs.

## Hypotheses beyond the paper

None in the H1 half. The J1 theorem `one_le_two_mul_noiseTraderLoss` takes
v4 Proposition 5.1's two conclusions — `W(V) ∈ L¹` and `Γ = E[W(V)]` — as
explicit hypotheses (`hint`, `hΓ`) rather than importing the accounting
module that proves them, exactly as v4's Proposition 6.1 invokes its
Proposition 5.1. `two_mul_noiseTraderLoss_id` discharges both at `φ = id`,
so the theorem is not vacuous.

All section, equation and lemma numbers refer to arXiv:2607.23585 **v4**
unless marked v3.
-/

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology

namespace KyleUniqueness

variable {φ : ℝ → ℝ}

/-! ## The critical point `c = F(0)` -/

/-- The paper's `c := F(0)` (inside the proof of v4 Proposition 6.1): the
unique point at which the insider submits the zero order. -/
noncomputable def criticalPoint (φ : ℝ → ℝ) : ℝ := gaussianSmoothing φ 0

theorem criticalPoint_def (φ : ℝ → ℝ) : criticalPoint φ = gaussianSmoothing φ 0 := rfl

/-- **v4 Proposition 6.1**: `φ(c) = 0`. Because `F` is strictly increasing,
`x ↦ x(c − F(x))` is negative for `x ≠ 0` and vanishes at `x = 0`, so `0` is
its unique maximiser; pointwise maximisation at `v = c` identifies `φ(c)`. -/
theorem strategy_criticalPoint (h : IsGammaSolution 0 φ) : φ (criticalPoint φ) = 0 := by
  have hc0 : gaussianSmoothing φ 0 = criticalPoint φ := rfl
  have hsm : StrictMono (gaussianSmoothing φ) :=
    strictMono_gaussianSmoothing_of_strictMono h.1 (strictMono_of_isGammaSolution h)
  have h0 : (0 : ℝ) ≤ φ (criticalPoint φ)
      * (criticalPoint φ - gaussianSmoothing φ (φ (criticalPoint φ))) := by
    have hle := h.2 (criticalPoint φ) 0
    rw [objective_zero] at hle
    simpa using hle
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlt' : gaussianSmoothing φ (φ (criticalPoint φ)) < criticalPoint φ := by
      rw [← hc0]; exact hsm hlt
    nlinarith
  · have hgt' : criticalPoint φ < gaussianSmoothing φ (φ (criticalPoint φ)) := by
      rw [← hc0]; exact hsm hgt
    nlinarith

/-- **v4 Proposition 6.1**, sign clause: `φ(v) < 0` for `v < c`. -/
theorem strategy_neg_of_lt_criticalPoint (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : v < criticalPoint φ) : φ v < 0 := by
  have := strictMono_of_isGammaSolution h hv
  rwa [strategy_criticalPoint h] at this

/-- **v4 Proposition 6.1**, sign clause: `φ(v) > 0` for `v > c`. -/
theorem strategy_pos_of_criticalPoint_lt (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : criticalPoint φ < v) : 0 < φ v := by
  have := strictMono_of_isGammaSolution h hv
  rwa [strategy_criticalPoint h] at this

/-- `φ ≥ 0` on `[c, ∞)` — the non-strict companion of the sign clause. -/
theorem strategy_nonneg_of_criticalPoint_le (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : criticalPoint φ ≤ v) : 0 ≤ φ v := by
  have := monotone_of_isGammaSolution h hv
  rwa [strategy_criticalPoint h] at this

/-- `φ ≤ 0` on `(−∞, c]` — the non-strict companion of the sign clause. -/
theorem strategy_nonpos_of_le_criticalPoint (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : v ≤ criticalPoint φ) : φ v ≤ 0 := by
  have := monotone_of_isGammaSolution h hv
  rwa [strategy_criticalPoint h] at this

/-! ## The posterior slope `q = F′ ∘ φ` -/

/-- The paper's `q(v) := F′(φ(v))` (inside the proof of v4 Proposition 6.1):
the slope of the Gaussian smoothing at the submitted order. -/
noncomputable def posteriorSlope (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  deriv (gaussianSmoothing φ) (φ v)

theorem posteriorSlope_apply (φ : ℝ → ℝ) (v : ℝ) :
    posteriorSlope φ v = deriv (gaussianSmoothing φ) (φ v) := rfl

/-- `q > 0` everywhere: v4 Lemma 2.5, eq. (2.8), composed with `φ`. -/
theorem posteriorSlope_pos (h : IsGammaSolution 0 φ) (v : ℝ) : 0 < posteriorSlope φ v :=
  deriv_gaussianSmoothing_pos_of_strictMono h.1 (strictMono_of_isGammaSolution h) (φ v)

/-- `q` is Borel (only Borel measurability of `φ` is used). -/
theorem measurable_posteriorSlope (hφ : Measurable φ) : Measurable (posteriorSlope φ) := by
  have hrw : posteriorSlope φ = fun v => deriv (gaussianSmoothing φ) (φ v) :=
    funext (posteriorSlope_apply φ)
  rw [hrw]
  exact (continuous_deriv_gaussianSmoothing hφ).measurable.comp hφ

/-- `q(V) ∈ L¹` — v4 Lemma 3.1, integrability clause. -/
theorem integrable_posteriorSlope (hφ : Measurable φ) :
    Integrable (posteriorSlope φ) (gaussianReal 0 1) :=
  integrable_deriv_gaussianSmoothing_comp hφ

/-- `Γ = E[q(V)]` — v4 Lemma 3.1, last equality. -/
theorem noiseTraderLoss_eq_integral_posteriorSlope (hφ : Measurable φ) :
    noiseTraderLoss φ = ∫ v, posteriorSlope φ v ∂(gaussianReal 0 1) :=
  noiseTraderLoss_eq_integral_deriv hφ

/-- **v4 Proposition 6.1**: `Γ > 0`, because `Γ = E[q(V)]` and `q(V) > 0`
almost surely. -/
theorem noiseTraderLoss_pos (h : IsGammaSolution 0 φ) : 0 < noiseTraderLoss φ := by
  rw [noiseTraderLoss_eq_integral_posteriorSlope h.1,
    integral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun v => (posteriorSlope_pos h v).le) (integrable_posteriorSlope h.1)]
  have hsupp : Function.support (posteriorSlope φ) = Set.univ := by
    ext v
    simp [Function.mem_support, (posteriorSlope_pos h v).ne']
  rw [hsupp, measure_univ]
  exact zero_lt_one

/-! ## The value function at, and away from, the critical point -/

/-- `W(c) = 0`: immediate from `W = φ²q` and `φ(c) = 0` (v4 eq. (2.5)). -/
theorem insiderProfit_criticalPoint (h : IsGammaSolution 0 φ) :
    insiderProfit φ (criticalPoint φ) = 0 := by
  rw [insiderProfit_eq_sq_mul_deriv h, strategy_criticalPoint h]
  ring

/-- `W(v) > 0` for `v ≠ c`: `W = φ²q` with `φ(v) ≠ 0` and `q(v) > 0`. -/
theorem insiderProfit_pos_of_ne (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : v ≠ criticalPoint φ) : 0 < insiderProfit φ v := by
  have hφ0 : φ v ≠ 0 := by
    rw [← strategy_criticalPoint h]
    exact fun hcon => hv ((strictMono_of_isGammaSolution h).injective hcon)
  rw [insiderProfit_eq_sq_mul_deriv h]
  exact mul_pos (sq_pos_of_ne_zero hφ0) (posteriorSlope_pos h v)

/-- `W` is strictly increasing on `[c, ∞)`: two applications of the
subgradient inequality (A.1) around an interior point, where `φ > 0`. -/
theorem insiderProfit_lt_of_criticalPoint_le (h : IsGammaSolution 0 φ) {v w : ℝ}
    (hv : criticalPoint φ ≤ v) (hvw : v < w) : insiderProfit φ v < insiderProfit φ w := by
  obtain ⟨m, hvm, hmw⟩ := exists_between hvw
  have hφm : 0 < φ m := strategy_pos_of_criticalPoint_lt h (lt_of_le_of_lt hv hvm)
  have hφv : 0 ≤ φ v := strategy_nonneg_of_criticalPoint_le h hv
  have h1 := insiderProfit_subgradient h v m
  have h2 := insiderProfit_subgradient h m w
  nlinarith [mul_pos hφm (sub_pos.2 hmw), mul_nonneg hφv (sub_pos.2 hvm).le]

/-- `W` is strictly decreasing on `(−∞, c]`: the mirror image of
`insiderProfit_lt_of_criticalPoint_le`, where `φ < 0`. -/
theorem insiderProfit_lt_of_le_criticalPoint (h : IsGammaSolution 0 φ) {v w : ℝ}
    (hvw : v < w) (hw : w ≤ criticalPoint φ) : insiderProfit φ w < insiderProfit φ v := by
  obtain ⟨m, hvm, hmw⟩ := exists_between hvw
  have hφm : φ m < 0 := strategy_neg_of_lt_criticalPoint h (lt_of_lt_of_le hmw hw)
  have hφw : φ w ≤ 0 := strategy_nonpos_of_le_criticalPoint h hw
  have h1 := insiderProfit_subgradient h m v
  have h2 := insiderProfit_subgradient h w m
  nlinarith [mul_pos_of_neg_of_neg hφm (sub_neg.2 hvm),
    mul_nonneg_of_nonpos_of_nonpos hφw (sub_nonpos.2 hmw.le)]

/-! ## The signed root `h` and the slope `r` -/

/-- The paper's `h(v) := sign(v − c)·√(2W(v))` (inside the proof of v4
Proposition 6.1): the odd square root of twice the value function, taken
negative below the critical point `c = F(0)`. -/
noncomputable def signedRoot (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  if v < criticalPoint φ then -Real.sqrt (2 * insiderProfit φ v)
  else Real.sqrt (2 * insiderProfit φ v)

/-- The paper's `r(v) := 1/√(2q(v))` (inside the proof of v4 Proposition
6.1): the a.e. derivative of the signed root. -/
noncomputable def rootSlope (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  (Real.sqrt (2 * posteriorSlope φ v))⁻¹

theorem signedRoot_apply (φ : ℝ → ℝ) (v : ℝ) :
    signedRoot φ v = if v < criticalPoint φ then -Real.sqrt (2 * insiderProfit φ v)
      else Real.sqrt (2 * insiderProfit φ v) := rfl

theorem rootSlope_apply (φ : ℝ → ℝ) (v : ℝ) :
    rootSlope φ v = (Real.sqrt (2 * posteriorSlope φ v))⁻¹ := rfl

theorem signedRoot_of_lt (φ : ℝ → ℝ) {v : ℝ} (hv : v < criticalPoint φ) :
    signedRoot φ v = -Real.sqrt (2 * insiderProfit φ v) := if_pos hv

theorem signedRoot_of_le (φ : ℝ → ℝ) {v : ℝ} (hv : criticalPoint φ ≤ v) :
    signedRoot φ v = Real.sqrt (2 * insiderProfit φ v) := if_neg (not_lt.2 hv)

/-- `r > 0` everywhere. -/
theorem rootSlope_pos (h : IsGammaSolution 0 φ) (v : ℝ) : 0 < rootSlope φ v :=
  inv_pos.2 (Real.sqrt_pos.2 (by linarith [posteriorSlope_pos h v]))

/-- `r` is Borel. -/
theorem measurable_rootSlope (hφ : Measurable φ) : Measurable (rootSlope φ) := by
  have hrw : rootSlope φ = fun v => (Real.sqrt (2 * posteriorSlope φ v))⁻¹ :=
    funext (rootSlope_apply φ)
  rw [hrw]
  have h1 : Measurable fun v => Real.sqrt (2 * posteriorSlope φ v) :=
    Real.continuous_sqrt.measurable.comp ((measurable_posteriorSlope hφ).const_mul 2)
  exact h1.inv

/-- `h` is Borel (no maximisation hypothesis needed). -/
theorem measurable_signedRoot (hφ : Measurable φ) : Measurable (signedRoot φ) := by
  have hrw : signedRoot φ = fun v =>
      if v < criticalPoint φ then -Real.sqrt (2 * insiderProfit φ v)
      else Real.sqrt (2 * insiderProfit φ v) := funext (signedRoot_apply φ)
  rw [hrw]
  have h1 : Measurable fun v => Real.sqrt (2 * insiderProfit φ v) :=
    Real.continuous_sqrt.measurable.comp ((measurable_insiderProfit hφ).const_mul 2)
  exact Measurable.ite measurableSet_Iio h1.neg h1

/-! ## The pointwise dictionary -/

/-- `h(v)² = 2W(v)` for **every** `v` (v4 Proposition 6.1). -/
theorem signedRoot_sq (h : IsGammaSolution 0 φ) (v : ℝ) :
    signedRoot φ v ^ 2 = 2 * insiderProfit φ v := by
  have hnn : 0 ≤ 2 * insiderProfit φ v := by linarith [insiderProfit_nonneg h v]
  rw [signedRoot_apply]
  by_cases hv : v < criticalPoint φ
  · rw [if_pos hv, neg_sq]
    exact Real.sq_sqrt hnn
  · rw [if_neg hv]
    exact Real.sq_sqrt hnn

/-- `1/r(v)² = 2q(v)` for **every** `v` (v4 Proposition 6.1). -/
theorem inv_rootSlope_sq (h : IsGammaSolution 0 φ) (v : ℝ) :
    (rootSlope φ v)⁻¹ ^ 2 = 2 * posteriorSlope φ v := by
  rw [rootSlope_apply, inv_inv]
  exact Real.sq_sqrt (by linarith [posteriorSlope_pos h v])

/-- `√(2W(v)) = |φ(v)|·√(2q(v))`: the factorisation `2W = φ²·(2q)` of
v4 eq. (2.5) under the square root. This is what turns the chain rule's
`sφ/√(2W)` into `1/√(2q)`. -/
theorem sqrt_two_mul_insiderProfit (h : IsGammaSolution 0 φ) (v : ℝ) :
    Real.sqrt (2 * insiderProfit φ v) = |φ v| * Real.sqrt (2 * posteriorSlope φ v) := by
  have hfac : 2 * insiderProfit φ v = φ v ^ 2 * (2 * posteriorSlope φ v) := by
    rw [insiderProfit_eq_sq_mul_deriv h, posteriorSlope_apply]
    ring
  rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-! ## Continuity and strict monotonicity of `h` -/

/-- `h(c) = 0`. -/
theorem signedRoot_criticalPoint (h : IsGammaSolution 0 φ) :
    signedRoot φ (criticalPoint φ) = 0 := by
  rw [signedRoot_of_le φ le_rfl, insiderProfit_criticalPoint h]
  simp

/-- `h` is continuous: the two branches agree at `c`, where `W(c) = 0`. -/
theorem continuous_signedRoot (h : IsGammaSolution 0 φ) : Continuous (signedRoot φ) := by
  have hsqrt : Continuous fun v => Real.sqrt (2 * insiderProfit φ v) :=
    (continuous_const.mul (continuous_insiderProfit h)).sqrt
  have hrw : signedRoot φ = fun v =>
      if criticalPoint φ ≤ v then Real.sqrt (2 * insiderProfit φ v)
      else -Real.sqrt (2 * insiderProfit φ v) := by
    funext v
    by_cases hv : v < criticalPoint φ
    · rw [signedRoot_of_lt φ hv, if_neg (not_le.2 hv)]
    · rw [signedRoot_of_le φ (not_lt.1 hv), if_pos (not_lt.1 hv)]
  rw [hrw]
  refine Continuous.if_le hsqrt hsqrt.neg continuous_const continuous_id fun x hx => ?_
  rw [← hx, insiderProfit_criticalPoint h]
  simp

/-- **v4 Proposition 6.1**: `h` is strictly increasing. Below `c` the value
function strictly decreases and the branch carries a minus sign; above `c` it
strictly increases; and the two branches are separated by `h(c) = 0`. -/
theorem strictMono_signedRoot (h : IsGammaSolution 0 φ) : StrictMono (signedRoot φ) := by
  intro v w hvw
  rcases lt_or_ge w (criticalPoint φ) with hw | hw
  · have hv : v < criticalPoint φ := hvw.trans hw
    rw [signedRoot_of_lt φ hv, signedRoot_of_lt φ hw, neg_lt_neg_iff]
    exact Real.sqrt_lt_sqrt (by linarith [insiderProfit_nonneg h w])
      (by linarith [insiderProfit_lt_of_le_criticalPoint h hvw hw.le])
  · rcases lt_or_ge v (criticalPoint φ) with hv | hv
    · rw [signedRoot_of_lt φ hv, signedRoot_of_le φ hw]
      have h1 : 0 < Real.sqrt (2 * insiderProfit φ v) :=
        Real.sqrt_pos.2 (by linarith [insiderProfit_pos_of_ne h (ne_of_lt hv)])
      have h2 : 0 ≤ Real.sqrt (2 * insiderProfit φ w) := Real.sqrt_nonneg _
      linarith
    · rw [signedRoot_of_le φ hv, signedRoot_of_le φ hw]
      exact Real.sqrt_lt_sqrt (by linarith [insiderProfit_nonneg h v])
        (by linarith [insiderProfit_lt_of_criticalPoint_le h hv hvw])

/-- `h` is nondecreasing — the form the Stein inequality consumes. -/
theorem monotone_signedRoot (h : IsGammaSolution 0 φ) : Monotone (signedRoot φ) :=
  (strictMono_signedRoot h).monotone

/-! ## The a.e. derivative `h′ = r` -/

/-- **v4 Proposition 6.1**, chain rule clause: at every `v ≠ c` at which `φ`
is continuous, `h` is differentiable with `h′(v) = r(v)`. -/
theorem hasDerivAt_signedRoot_of_ne (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : v ≠ criticalPoint φ) (hcont : ContinuousAt φ v) :
    HasDerivAt (signedRoot φ) (rootSlope φ v) v := by
  have hWpos : 0 < insiderProfit φ v := insiderProfit_pos_of_ne h hv
  have hne : (fun u => 2 * insiderProfit φ u) v ≠ 0 := by
    simp only
    exact ne_of_gt (by linarith)
  have hsq : HasDerivAt (fun u => Real.sqrt (2 * insiderProfit φ u))
      (2 * φ v / (2 * Real.sqrt (2 * insiderProfit φ v))) v :=
    ((hasDerivAt_insiderProfit_of_continuousAt h hcont).const_mul 2).sqrt hne
  have hspos : Real.sqrt (2 * posteriorSlope φ v) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith [posteriorSlope_pos h v]))
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have hφv : φ v < 0 := strategy_neg_of_lt_criticalPoint h hlt
    have hval : -(2 * φ v / (2 * Real.sqrt (2 * insiderProfit φ v))) = rootSlope φ v := by
      rw [sqrt_two_mul_insiderProfit h, abs_of_neg hφv, rootSlope_apply]
      field_simp [hφv.ne, hspos]
    have hneg : HasDerivAt (fun u => -Real.sqrt (2 * insiderProfit φ u))
        (-(2 * φ v / (2 * Real.sqrt (2 * insiderProfit φ v)))) v := hsq.neg
    rw [← hval]
    refine hneg.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hlt] with u hu
    rw [signedRoot_of_lt φ hu]
  · have hφv : 0 < φ v := strategy_pos_of_criticalPoint_lt h hgt
    have hval : 2 * φ v / (2 * Real.sqrt (2 * insiderProfit φ v)) = rootSlope φ v := by
      rw [sqrt_two_mul_insiderProfit h, abs_of_pos hφv, rootSlope_apply]
      field_simp [hφv.ne', hspos]
    rw [← hval]
    refine hsq.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hgt] with u hu
    rw [signedRoot_of_le φ (le_of_lt hu)]

/-- **v4 Proposition 6.1**: `h′ = r` Lebesgue-almost everywhere. The
exceptional set is `{c}` together with the discontinuity set of the monotone
`φ`, which is countable, hence null. -/
theorem ae_hasDerivAt_signedRoot (h : IsGammaSolution 0 φ) :
    ∀ᵐ v ∂(volume : Measure ℝ), HasDerivAt (signedRoot φ) (rootSlope φ v) v := by
  filter_upwards [(monotone_of_isGammaSolution h).countable_not_continuousAt.ae_notMem volume,
    (Set.countable_singleton (criticalPoint φ)).ae_notMem (volume : Measure ℝ)] with v hv hc
  exact hasDerivAt_signedRoot_of_ne h (by simpa using hc) (not_not.1 hv)

/-! ## The moment identities -/

/-- `h(V)² ∈ L¹ ↔ W(V) ∈ L¹`, by the pointwise identity `h² = 2W`. -/
theorem integrable_sq_signedRoot_iff (h : IsGammaSolution 0 φ) :
    Integrable (fun v => signedRoot φ v ^ 2) (gaussianReal 0 1)
      ↔ Integrable (insiderProfit φ) (gaussianReal 0 1) := by
  have hrw : (fun v => signedRoot φ v ^ 2) = fun v => 2 * insiderProfit φ v :=
    funext (signedRoot_sq h)
  rw [hrw]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 two_ne_zero) _

/-- **v4 Proposition 6.1**: `E[h(V)²] = 2·E[W(V)]`. -/
theorem integral_sq_signedRoot (h : IsGammaSolution 0 φ) :
    ∫ v, signedRoot φ v ^ 2 ∂(gaussianReal 0 1)
      = 2 * ∫ v, insiderProfit φ v ∂(gaussianReal 0 1) := by
  rw [integral_congr_ae (ae_of_all _ (signedRoot_sq h)), integral_const_mul]

/-- `1/r(V)² ∈ L¹`, by the pointwise identity `1/r² = 2q` and v4 Lemma 3.1. -/
theorem integrable_inv_sq_rootSlope (h : IsGammaSolution 0 φ) :
    Integrable (fun v => (rootSlope φ v)⁻¹ ^ 2) (gaussianReal 0 1) := by
  have hrw : (fun v => (rootSlope φ v)⁻¹ ^ 2) = fun v => 2 * posteriorSlope φ v :=
    funext (inv_rootSlope_sq h)
  rw [hrw]
  exact (integrable_posteriorSlope h.1).const_mul 2

/-- **v4 Proposition 6.1**: `E[1/r(V)²] = 2·E[q(V)] = 2Γ`. -/
theorem integral_inv_sq_rootSlope (h : IsGammaSolution 0 φ) :
    ∫ v, (rootSlope φ v)⁻¹ ^ 2 ∂(gaussianReal 0 1) = 2 * noiseTraderLoss φ := by
  rw [integral_congr_ae (ae_of_all _ (inv_rootSlope_sq h)), integral_const_mul,
    noiseTraderLoss_eq_integral_posteriorSlope h.1]

/-! ## J1: `1 ≤ 2Γ` -/

/-- **Node J1 = the second half of v4 Proposition 6.1**: `Γ ≥ 1/2`.

The two conclusions of v4 Proposition 5.1 — `W(V) ∈ L¹` (`hint`) and
`Γ = E[W(V)]` (`hΓ`) — enter as explicit hypotheses. Given them, the banked
one-sided Stein inequality (v3 Lemma 2.5, blueprint nodes I1–I3) applied to
the monotone `h` with a.e. derivative `r > 0` gives
`1 ≤ √(E[h(V)²]·E[1/r(V)²]) = √((2Γ)·(2Γ)) = 2Γ`,
the last step because `Γ > 0`.

(Lane-C decision D7: v4 itself routes this through its Lemma 2.7, Cacoullos'
inequality, plus a truncation argument. The Stein inequality proves the same
bound directly.) -/
theorem one_le_two_mul_noiseTraderLoss (h : IsGammaSolution 0 φ)
    (hint : Integrable (insiderProfit φ) (gaussianReal 0 1))
    (hΓ : noiseTraderLoss φ = ∫ v, insiderProfit φ v ∂(gaussianReal 0 1)) :
    1 ≤ 2 * noiseTraderLoss φ := by
  have hstein := one_le_sqrt_integral_sq_mul_integral_inv_sq
    (f := signedRoot φ) (f' := rootSlope φ) (monotone_signedRoot h)
    (ae_hasDerivAt_signedRoot h) (ae_of_all _ (rootSlope_pos h))
    ((integrable_sq_signedRoot_iff h).2 hint) (integrable_inv_sq_rootSlope h)
  rw [integral_sq_signedRoot h, integral_inv_sq_rootSlope h, ← hΓ,
    Real.sqrt_mul_self (by linarith [noiseTraderLoss_pos h])] at hstein
  exact hstein

/-! ## Sanity oracles at `φ = id` -/

/-- The Kyle strategy `φ = id` satisfies the pointwise maximisation
condition: with `F(x) = x/2` (`gaussianSmoothing_id`) the objective is
`xv − x²/2`, uniquely maximised at `x = v`. (Re-proved here rather than
imported, so that nothing in this file depends on the still-open rigidity
direction of `isGammaSolution_zero_iff`.) -/
theorem isGammaSolution_zero_id : IsGammaSolution 0 (id : ℝ → ℝ) := by
  refine ⟨measurable_id, fun v x => ?_⟩
  simp only [objective, gaussianSmoothing_id, id_eq]
  nlinarith [sq_nonneg (v - x)]

/-- Oracle: `c = F(0) = 0` at `φ = id`. -/
theorem criticalPoint_id : criticalPoint (id : ℝ → ℝ) = 0 := by
  rw [criticalPoint_def, gaussianSmoothing_id]
  norm_num

/-- Oracle: `q ≡ 1/2` at `φ = id`. -/
theorem posteriorSlope_id : posteriorSlope (id : ℝ → ℝ) = fun _ => 1 / 2 := by
  funext v
  rw [posteriorSlope_apply, gaussianSmoothing_id]
  simp

/-- Oracle: `h = id` at `φ = id` (the signed root of `2·(v²/2) = v²`). -/
theorem signedRoot_id : signedRoot (id : ℝ → ℝ) = fun v => v := by
  funext v
  rw [signedRoot_apply, criticalPoint_id, insiderProfit_id]
  have h2 : 2 * (v ^ 2 / 2) = v ^ 2 := by ring
  simp only
  rw [h2, Real.sqrt_sq_eq_abs]
  by_cases hv : v < 0
  · rw [if_pos hv, abs_of_neg hv, neg_neg]
  · rw [if_neg hv, abs_of_nonneg (not_lt.1 hv)]

/-- Oracle: `r ≡ 1` at `φ = id`. -/
theorem rootSlope_id : rootSlope (id : ℝ → ℝ) = fun _ => 1 := by
  funext v
  rw [rootSlope_apply, posteriorSlope_id]
  norm_num

/-- Oracle: `W(V) = V²/2 ∈ L¹` at `φ = id`. -/
theorem integrable_insiderProfit_id :
    Integrable (insiderProfit (id : ℝ → ℝ)) (gaussianReal 0 1) := by
  rw [insiderProfit_id]
  exact integrable_sq_gaussianReal_std.div_const 2

/-- Oracle: `E[W(V)] = E[V²]/2 = 1/2` at `φ = id`, **via the closed form**
`insiderProfit id = fun v => v ^ 2 / 2` (`insiderProfit_id`).
`KyleUniqueness.Accounting.integral_insiderProfit_id` proves the very same
identity by the *other* route, feeding `φ = id` to `accounting_identity`.
The two routes are independent, so keeping both is a genuine cross-check;
the `_of_closedForm` suffix says which route this one is (it was originally
distinguished only by a prime, which told a reader nothing). -/
theorem integral_insiderProfit_id_of_closedForm :
    ∫ v, insiderProfit (id : ℝ → ℝ) v ∂(gaussianReal 0 1) = 1 / 2 := by
  have hsq : (fun v : ℝ => v ^ 2) = fun v : ℝ => v * v := funext fun v => sq v
  rw [insiderProfit_id]
  simp only
  rw [integral_div, hsq, integral_mul_self_gaussianReal_std]

/-- Oracle: `2Γ = 1` at `φ = id` (`noiseTraderLoss_id`), so the J1 bound is
attained — in particular `one_le_two_mul_noiseTraderLoss` is not vacuous. -/
theorem two_mul_noiseTraderLoss_id : 2 * noiseTraderLoss (id : ℝ → ℝ) = 1 := by
  rw [noiseTraderLoss_id]
  norm_num

/-- Oracle: the J1 theorem instantiated at `φ = id`, with both Proposition
5.1 hypotheses discharged. Together with `two_mul_noiseTraderLoss_id` this
witnesses that the bound `1 ≤ 2Γ` is tight. -/
theorem one_le_two_mul_noiseTraderLoss_id : 1 ≤ 2 * noiseTraderLoss (id : ℝ → ℝ) :=
  one_le_two_mul_noiseTraderLoss isGammaSolution_zero_id integrable_insiderProfit_id
    (noiseTraderLoss_id.trans integral_insiderProfit_id_of_closedForm.symm)

end KyleUniqueness
