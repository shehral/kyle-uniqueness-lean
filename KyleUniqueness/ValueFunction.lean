/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.Regularity
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The insider's value function `W` (blueprint nodes B1 + B2; v4 Lemma 2.4)

Formalization of **Lemma 2.4** of Monteiro & Tourky, *The one-period Kyle
model has one equilibrium* (arXiv:2607.23585, **v4** of
2026-08-20; = v3 Lemma 2.6), together with the subgradient inequality (A.1)
from the appendix proof of that lemma.

## The definition of `W` (Lane-C decision D2)

v4 §2.4 defines the value function by the literal supremum
`W(v) := sup_{x ∈ ℝ} x (v − F(x))`, allowing the value `+∞`. We instead
define `insiderProfit φ v := objective 0 φ v (φ v)`, the *attained* value at
the paper's maximiser. Under the standing hypothesis `IsGammaSolution 0 φ`
(the paper's `φ(v) ∈ argmax_x x(v − F(x))` for every `v`, v3 condition (17))
the two agree; this is `insiderProfit_eq_iSup`, the mandatory faithfulness
bridge. The attainment form is total and junk-free, is Borel in one line
(v4 Lemma 3.2 = `measurable_insiderProfit`), and keeps every downstream
consumer in `ℝ` rather than `EReal`.

## Main statements (all under `h : IsGammaSolution 0 φ` unless noted)

* `isMaxOn_objective` — the hypothesis in Mathlib's `IsMaxOn` packaging;
* `insiderProfit_eq_iSup` — the faithfulness bridge to v4 §2.4's literal sup;
* `measurable_insiderProfit` — v4 Lemma 3.2 (needs only `Measurable φ`);
* `insiderProfit_nonneg` — `W ≥ 0` (v4 §2.4: `x = 0` is admissible);
* `insiderProfit_subgradient` — the subgradient inequality **(A.1)**,
  `W(v) + φ(v)(w − v) ≤ W(w)`;
* `convexOn_insiderProfit` — `W` is convex (v4 §2.4);
* `monotone_of_isGammaSolution` — `φ` is nondecreasing, from (A.1) alone;
* `firstOrderCondition` — **(2.4)**, `F(φ(v)) + φ(v)F′(φ(v)) = v`;
* `insiderProfit_eq_sq_mul_deriv` — **(2.5)**, `W(v) = φ(v)²F′(φ(v))`;
* `strictMono_of_isGammaSolution` — `φ` is strictly increasing;
* `continuous_insiderProfit` — `W` is continuous;
* `ae_hasDerivAt_insiderProfit` — **(2.6)**, `W′ = φ` Lebesgue-a.e.;
* `hasDerivWithinAt_Ioi_insiderProfit` — the everywhere right derivative
  `rightLim φ` (strengthening of (2.6) that drives the next item);
* `insiderProfit_sub_eq_intervalIntegral` — local absolute continuity in the
  form actually consumed downstream, `W(b) − W(a) = ∫_a^b φ`;
* `insiderProfit_id` — the sanity oracle `W = v ↦ v²/2` at `φ = id`.

Auxiliary exports: `objective_zero`, `insiderProfit_apply` (`simp`),
`objective_le_insiderProfit`, `continuous_gaussianSmoothing`,
`insiderProfit_sub_sandwich` (the two-sided (A.1)),
`hasDerivAt_insiderProfit_of_continuousAt`,
`intervalIntegrable_of_isGammaSolution`.

## Route

No hypothesis beyond the paper's is added. `F ∈ C¹` is imported from
`KyleUniqueness.Regularity` (node R2 = v4 Lemma 2.3). (A.1) is two
applications of the maximisation hypothesis; convexity, monotonicity and the
slope squeeze are then elementary consequences of (A.1). (2.4) is
`IsLocalMax.hasDerivAt_eq_zero` against the `C¹` objective, and (2.5) is one
substitution. For continuity we use Mathlib's `ConvexOn.continuousOn` rather
than the paper's citation to Rockafellar. For (2.6) the two-sided form of
(A.1) squeezes `slope W v` between `min (φ v) (φ w)` and `max (φ v) (φ w)`,
which pins the derivative at every continuity point of `φ`; the exceptional
set is countable by `Monotone.countable_not_continuousAt`, hence Lebesgue
null. The absolute-continuity surrogate replaces "locally absolutely
continuous" by the interval-integral identity it is used for: `W` has the
right derivative `rightLim φ` *everywhere* (same squeeze, plus a one-sided
limit of (A.1) applied at interior points), so
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` applies with the
monotone — hence interval-integrable — integrand `rightLim φ`, which agrees
with `φ` off the countable discontinuity set.

All section, equation and lemma numbers refer to arXiv:2607.23585 **v4**
unless marked v3.
-/

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology

namespace KyleUniqueness

variable {φ : ℝ → ℝ}

/-! ## The value function -/

/-- The insider's **attained** profit at the observed value `v`:
`Π(v) = φ(v)·(v − F(φ(v)))`, the objective of v3 eq. (8) evaluated at the
paper's maximiser. Under `IsGammaSolution 0 φ` this is the paper's value
function `W(v) = sup_x x(v − F(x))` of v4 §2.4 — see `insiderProfit_eq_iSup`
— and it is the quantity v4 Prop. 5.1 calls `Π`. -/
noncomputable def insiderProfit (φ : ℝ → ℝ) (v : ℝ) : ℝ := objective 0 φ v (φ v)

/-- The blueprint's name `W` for `insiderProfit` (v4 §2.4). -/
noncomputable abbrev valueFunction := insiderProfit

/-- `objective 0` is the paper's bare objective `x ↦ x(v − F(x))`; the
`γ`-quadratic penalty of the beyond-paper family vanishes at `γ = 0`. -/
theorem objective_zero (φ : ℝ → ℝ) (v : ℝ) :
    objective 0 φ v = fun x => x * (v - gaussianSmoothing φ x) := by
  funext x
  simp [objective]

@[simp]
theorem insiderProfit_apply (φ : ℝ → ℝ) (v : ℝ) :
    insiderProfit φ v = φ v * (v - gaussianSmoothing φ (φ v)) := by
  rw [insiderProfit, objective_zero]

/-! ## The maximisation hypothesis, and the bridge to the paper's supremum -/

/-- v3 condition (17) in Mathlib's `IsMaxOn` packaging: `φ v` maximises the
objective `x ↦ x(v − F(x))` over all of `ℝ`. -/
theorem isMaxOn_objective (h : IsGammaSolution 0 φ) (v : ℝ) :
    IsMaxOn (objective 0 φ v) Set.univ (φ v) :=
  isMaxOn_univ_iff.2 (h.2 v)

/-- The maximisation hypothesis phrased against `insiderProfit`: no order is
better than the one the strategy submits. -/
theorem objective_le_insiderProfit (h : IsGammaSolution 0 φ) (v x : ℝ) :
    objective 0 φ v x ≤ insiderProfit φ v :=
  h.2 v x

/-- **Faithfulness bridge (Lane-C decision D2).** Under the maximisation
hypothesis, the attainment form `insiderProfit` agrees with the literal
supremum `W(v) = sup_{x ∈ ℝ} x(v − F(x))` by which v4 §2.4 defines the value
function. (v4 notes that the supremum is real-valued precisely because it is
attained, which is exactly the content of this lemma.) -/
theorem insiderProfit_eq_iSup (h : IsGammaSolution 0 φ) (v : ℝ) :
    insiderProfit φ v = ⨆ x : ℝ, objective 0 φ v x := by
  have hb : BddAbove (Set.range (objective 0 φ v)) := by
    refine ⟨objective 0 φ v (φ v), ?_⟩
    rintro y ⟨x, rfl⟩
    exact h.2 v x
  refine le_antisymm ?_ (ciSup_le fun x => h.2 v x)
  exact le_ciSup hb (φ v)

/-! ## Borel measurability (v4 Lemma 3.2) -/

/-- The Gaussian smoothing is continuous, as the `C¹` clause of v4 Lemma 2.3
(node R2, `KyleUniqueness.Regularity`) gives it a derivative everywhere. -/
theorem continuous_gaussianSmoothing (hφ : Measurable φ) :
    Continuous (gaussianSmoothing φ) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_gaussianSmoothing hφ x).continuousAt

/-- **v4 Lemma 3.2**: `Π = insiderProfit φ` is Borel. Only Borel measurability
of `φ` is needed (plus continuity of `F`), not the maximisation hypothesis. -/
theorem measurable_insiderProfit (hφ : Measurable φ) : Measurable (insiderProfit φ) := by
  have hrw : insiderProfit φ = fun v => φ v * (v - gaussianSmoothing φ (φ v)) :=
    funext (insiderProfit_apply φ)
  rw [hrw]
  exact hφ.mul (measurable_id.sub ((continuous_gaussianSmoothing hφ).measurable.comp hφ))

/-! ## Nonnegativity and the subgradient inequality (A.1) -/

/-- v4 §2.4: `W ≥ 0`, "because `x = 0` is admissible". -/
theorem insiderProfit_nonneg (h : IsGammaSolution 0 φ) (v : ℝ) : 0 ≤ insiderProfit φ v := by
  have h0 := h.2 v 0
  rw [objective_zero] at h0
  simpa using h0

/-- **Inequality (A.1)** (appendix proof of v4 Lemma 2.4): `φ(v)` is a
subgradient of `W` at `v`, i.e. `W(w) ≥ W(v) + φ(v)(w − v)` for all `v, w`.
Immediate from maximisation: the order `φ(v)` is admissible at `w`. -/
theorem insiderProfit_subgradient (h : IsGammaSolution 0 φ) (v w : ℝ) :
    insiderProfit φ v + φ v * (w - v) ≤ insiderProfit φ w := by
  have hmax := h.2 w (φ v)
  rw [objective_zero] at hmax
  simp only [insiderProfit_apply]
  nlinarith [hmax]

/-- The two-sided form of (A.1): the increment of `W` is squeezed between the
two subgradients at the endpoints. This is the workhorse behind monotonicity,
convexity, continuity and eq. (2.6). -/
theorem insiderProfit_sub_sandwich (h : IsGammaSolution 0 φ) (v w : ℝ) :
    φ v * (w - v) ≤ insiderProfit φ w - insiderProfit φ v ∧
      insiderProfit φ w - insiderProfit φ v ≤ φ w * (w - v) := by
  constructor
  · linarith [insiderProfit_subgradient h v w]
  · linarith [insiderProfit_subgradient h w v]

/-! ## Convexity, monotonicity -/

/-- v4 §2.4: `W` is convex. (The paper gets this from the representation as a
pointwise supremum of affine functions; with the attainment form it follows
from the subgradient inequality (A.1).) -/
theorem convexOn_insiderProfit (h : IsGammaSolution 0 φ) :
    ConvexOn ℝ Set.univ (insiderProfit φ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  have hx := insiderProfit_subgradient h (a * x + (1 - a) * y) x
  have hy := insiderProfit_subgradient h (a * x + (1 - a) * y) y
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- **v4 Lemma 2.4, monotonicity clause**: a pointwise maximiser is
nondecreasing. Proof as in the appendix: add (A.1) in both directions. -/
theorem monotone_of_isGammaSolution (h : IsGammaSolution 0 φ) : Monotone φ := by
  intro v w hvw
  rcases eq_or_lt_of_le hvw with rfl | hlt
  · exact le_rfl
  · have h1 := insiderProfit_subgradient h v w
    have h2 := insiderProfit_subgradient h w v
    nlinarith [h1, h2, sub_pos.2 hlt]

/-! ## The first-order condition (2.4) and the identity (2.5) -/

/-- **v4 Lemma 2.4, eq. (2.4)** — the first-order condition:
`F(φ(v)) + φ(v)·F′(φ(v)) = v` for every `v`. The objective is `C¹` by v4
Lemma 2.3 (node R2) and is maximised at `φ(v)`, so its derivative vanishes
there. -/
theorem firstOrderCondition (h : IsGammaSolution 0 φ) (v : ℝ) :
    gaussianSmoothing φ (φ v) + φ v * deriv (gaussianSmoothing φ) (φ v) = v := by
  have hφ : Measurable φ := h.1
  have hF : HasDerivAt (gaussianSmoothing φ) (deriv (gaussianSmoothing φ) (φ v)) (φ v) := by
    rw [deriv_gaussianSmoothing hφ]
    exact hasDerivAt_gaussianSmoothing hφ (φ v)
  have hd : HasDerivAt (objective 0 φ v)
      (1 * (v - gaussianSmoothing φ (φ v))
        + φ v * -deriv (gaussianSmoothing φ) (φ v)) (φ v) := by
    rw [objective_zero]
    exact (hasDerivAt_id (φ v)).mul (hF.const_sub v)
  have hmax : IsLocalMax (objective 0 φ v) (φ v) :=
    (isMaxOn_objective h v).isLocalMax Filter.univ_mem
  have hzero := hmax.hasDerivAt_eq_zero hd
  linarith [hzero]

/-- **v4 Lemma 2.4, eq. (2.5)**: `W(v) = φ(v)²·F′(φ(v))`. -/
theorem insiderProfit_eq_sq_mul_deriv (h : IsGammaSolution 0 φ) (v : ℝ) :
    insiderProfit φ v = φ v ^ 2 * deriv (gaussianSmoothing φ) (φ v) := by
  rw [insiderProfit_apply]
  linear_combination (-(φ v)) * firstOrderCondition h v

/-- **v4 Lemma 2.4, final clause**: a pointwise maximiser is *strictly*
increasing. Monotone by `monotone_of_isGammaSolution`, and injective because
(2.4) recovers `v` from `φ(v)`. -/
theorem strictMono_of_isGammaSolution (h : IsGammaSolution 0 φ) : StrictMono φ := by
  refine (monotone_of_isGammaSolution h).strictMono_of_injective fun v w hvw => ?_
  have h1 := firstOrderCondition h v
  have h2 := firstOrderCondition h w
  rw [hvw] at h1
  linarith [h1, h2]

/-! ## Continuity and the a.e. derivative (2.6) -/

/-- `W` is continuous: a finite convex function on `ℝ` is locally Lipschitz.
(v4 §2.4 cites Rockafellar for "locally absolutely continuous"; Mathlib's
`ConvexOn.continuousOn` supplies the continuity half directly.) -/
theorem continuous_insiderProfit (h : IsGammaSolution 0 φ) :
    Continuous (insiderProfit φ) := by
  rw [← continuousOn_univ]
  exact (convexOn_insiderProfit h).continuousOn isOpen_univ

/-- The slope of `W` at `v` lies between `φ v` and `φ w`: the two-sided form
of (A.1), divided by `w − v`. -/
private lemma slope_insiderProfit_mem (h : IsGammaSolution 0 φ) {v w : ℝ} (hw : w ≠ v) :
    min (φ v) (φ w) ≤ slope (insiderProfit φ) v w ∧
      slope (insiderProfit φ) v w ≤ max (φ v) (φ w) := by
  obtain ⟨h1, h2⟩ := insiderProfit_sub_sandwich h v w
  rw [slope_def_field]
  rcases lt_or_gt_of_ne hw with hlt | hgt
  · have hneg : w - v < 0 := by linarith
    refine ⟨?_, ?_⟩
    · rw [le_div_iff_of_neg hneg]
      nlinarith [h2, min_le_right (φ v) (φ w)]
    · rw [div_le_iff_of_neg hneg]
      nlinarith [h1, le_max_left (φ v) (φ w)]
  · have hpos : 0 < w - v := by linarith
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hpos]
      nlinarith [h1, min_le_left (φ v) (φ w)]
    · rw [div_le_iff₀ hpos]
      nlinarith [h2, le_max_right (φ v) (φ w)]

/-- At every continuity point of `φ`, the value function is differentiable
with `W′(v) = φ(v)` (the pointwise form of v4 eq. (2.6)). -/
theorem hasDerivAt_insiderProfit_of_continuousAt (h : IsGammaSolution 0 φ) {v : ℝ}
    (hv : ContinuousAt φ v) : HasDerivAt (insiderProfit φ) (φ v) v := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hφ : Tendsto φ (𝓝[≠] v) (𝓝 (φ v)) := hv.tendsto.mono_left nhdsWithin_le_nhds
  have hcmin : Continuous fun y : ℝ => min (φ v) y := continuous_const.min continuous_id
  have hcmax : Continuous fun y : ℝ => max (φ v) y := continuous_const.max continuous_id
  have hmin : Tendsto (fun w => min (φ v) (φ w)) (𝓝[≠] v) (𝓝 (φ v)) := by
    have := (hcmin.tendsto (φ v)).comp hφ
    simpa [Function.comp_def] using this
  have hmax : Tendsto (fun w => max (φ v) (φ w)) (𝓝[≠] v) (𝓝 (φ v)) := by
    have := (hcmax.tendsto (φ v)).comp hφ
    simpa [Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact (slope_insiderProfit_mem h hw).1
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact (slope_insiderProfit_mem h hw).2

/-- **v4 Lemma 2.4, eq. (2.6)**: `W′(v) = φ(v)` for Lebesgue-almost every
`v`. The exceptional set is the discontinuity set of the monotone map `φ`,
which is countable hence null. -/
theorem ae_hasDerivAt_insiderProfit (h : IsGammaSolution 0 φ) :
    ∀ᵐ v ∂(volume : Measure ℝ), HasDerivAt (insiderProfit φ) (φ v) v := by
  filter_upwards [(monotone_of_isGammaSolution h).countable_not_continuousAt.ae_notMem volume]
    with v hv
  exact hasDerivAt_insiderProfit_of_continuousAt h (not_not.1 hv)

/-! ## Local absolute continuity, as the interval-integral identity -/

/-- The right-hand subgradient bound: taking `u ↓ v` in (A.1) applied at
interior points `u ∈ (v, w)` upgrades `φ v` to `rightLim φ v`. -/
private lemma rightLim_mul_le_sub (h : IsGammaSolution 0 φ) {v w : ℝ} (hvw : v < w) :
    Function.rightLim φ v * (w - v) ≤ insiderProfit φ w - insiderProfit φ v := by
  have hmono := monotone_of_isGammaSolution h
  have hcont : Continuous
      fun u : ℝ => Function.rightLim φ v * (w - u) + φ v * (u - v) := by fun_prop
  have htend : Tendsto (fun u : ℝ => Function.rightLim φ v * (w - u) + φ v * (u - v))
      (𝓝[>] v) (𝓝 (Function.rightLim φ v * (w - v) + φ v * (v - v))) :=
    (hcont.tendsto v).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in 𝓝[>] v, Function.rightLim φ v * (w - u) + φ v * (u - v)
      ≤ insiderProfit φ w - insiderProfit φ v := by
    filter_upwards [Ioo_mem_nhdsGT hvw] with u hu
    have h1 := insiderProfit_subgradient h u w
    have h2 := insiderProfit_subgradient h v u
    have h4 : 0 ≤ (φ u - Function.rightLim φ v) * (w - u) :=
      mul_nonneg (sub_nonneg.2 (hmono.rightLim_le hu.1)) (sub_pos.2 hu.2).le
    nlinarith [h1, h2, h4]
  simpa using le_of_tendsto htend hev

/-- `W` has a right derivative at **every** point, equal to `rightLim φ` —
the honest pointwise content of v4's "`W` is locally absolutely continuous".
(At a continuity point of `φ` this is `hasDerivAt_insiderProfit_of_continuousAt`
restricted to `Ioi`; the jump points of the monotone `φ` are exactly where the
right derivative `rightLim φ v` exceeds `φ v`.) -/
theorem hasDerivWithinAt_Ioi_insiderProfit (h : IsGammaSolution 0 φ) (v : ℝ) :
    HasDerivWithinAt (insiderProfit φ) (Function.rightLim φ v) (Ioi v) v := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((monotone_of_isGammaSolution h).tendsto_rightLim v) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    have hvw : v < w := hw
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hvw)]
    linarith [rightLim_mul_le_sub h hvw]
  · filter_upwards [self_mem_nhdsWithin] with w hw
    have hvw : v < w := hw
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hvw)]
    linarith [(insiderProfit_sub_sandwich h v w).2]

/-- A pointwise maximiser is interval-integrable, being monotone. (Companion
to `insiderProfit_sub_eq_intervalIntegral`: it de-vacuates the right-hand
side of that identity.) -/
theorem intervalIntegrable_of_isGammaSolution (h : IsGammaSolution 0 φ) (a b : ℝ) :
    IntervalIntegrable φ volume a b :=
  (monotone_of_isGammaSolution h).intervalIntegrable

/-- **v4 Lemma 2.4, local absolute continuity**, in the form its consumers
need: `W(b) − W(a) = ∫_a^b φ(v) dv` for all `a, b`. -/
theorem insiderProfit_sub_eq_intervalIntegral (h : IsGammaSolution 0 φ) (a b : ℝ) :
    insiderProfit φ b - insiderProfit φ a = ∫ v in a..b, φ v := by
  have hmono := monotone_of_isGammaSolution h
  have hrl : ∀ᵐ v ∂(volume : Measure ℝ), Function.rightLim φ v = φ v := by
    filter_upwards [hmono.countable_not_continuousAt.ae_notMem volume] with v hv
    exact hmono.continuousWithinAt_Ioi_iff_rightLim_eq.1 (not_not.1 hv).continuousWithinAt
  have key : ∀ x y : ℝ, x ≤ y →
      insiderProfit φ y - insiderProfit φ x = ∫ v in x..y, φ v := by
    intro x y hxy
    have hcongr : ∫ v in x..y, Function.rightLim φ v = ∫ v in x..y, φ v :=
      intervalIntegral.integral_congr_ae (by filter_upwards [hrl] with v hv using fun _ => hv)
    rw [← hcongr]
    exact (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxy
      (continuous_insiderProfit h).continuousOn
      (fun t _ => hasDerivWithinAt_Ioi_insiderProfit h t)
      hmono.rightLim.intervalIntegrable).symm
  rcases le_total a b with hab | hab
  · exact key a b hab
  · rw [intervalIntegral.integral_symm b a]
    linarith [key b a hab]

/-! ## Sanity oracle -/

/-- Sanity oracle: for the Kyle equilibrium strategy `φ = id` (whose Gaussian
smoothing is `F(x) = x/2`, `gaussianSmoothing_id`) the value function is
`W(v) = v²/2`. No hypothesis is needed: this is a computation. -/
theorem insiderProfit_id : insiderProfit id = fun v => v ^ 2 / 2 := by
  funext v
  rw [insiderProfit_apply, gaussianSmoothing_id]
  simp only [id_eq]
  ring

end KyleUniqueness
