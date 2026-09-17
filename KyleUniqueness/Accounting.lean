/-
Copyright (c) 2026 Mohammad Ali Shehral. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammad Ali Shehral
-/
import KyleUniqueness.ValueFunction
import KyleUniqueness.Posterior
import KyleUniqueness.Resampling
import KyleUniqueness.Loss

/-!
# The accounting identity `Γ = E[Π(V)]` (blueprint node E2; v4 Proposition 5.1)

Formalization of **Proposition 5.1** of Monteiro & Tourky, *The one-period
Gaussian Kyle model has exactly one equilibrium* (arXiv:2607.23585, **v4** of
2026-08-20; = blueprint node E2, Lane-C decision D6), together with the
equations (5.1)–(5.3) of its proof:

> If `φ` is nondecreasing and `Π(V) ≥ 0` almost surely, then `Π(V) ∈ L¹` and
> `Γ = E[Π(V)]`.

Here `Γ = noiseTraderLoss φ` is the noise traders' expected loss (v4 §3.1) and
`Π = insiderProfit φ` is the insider's attained profit
`Π(v) = φ(v)(v − F(φ(v)))` (`ValueFunction.lean`, decision D2; v4 §2.4's `W`
under the maximisation hypothesis). No integrability assumption on `φ(V)` or
`Π(V)` is made anywhere: the lattice truncation supplies it.

## Set-up

`μ₃ = resamplingMeasure φ` (`Resampling.lean`, v4 Lemma 2.6) is the law of the
exchangeable triple `(V⁰, V¹, Y)` on `ℝ × ℝ × ℝ` with coordinates
`q.1 = v₀`, `q.2.1 = v₁`, `q.2.2 = y`; the noises are
`U⁰ = q.2.2 − φ q.1` and `U¹ = q.2.2 − φ q.2.1`. The truncation `φₙ` of v4
Part II is `clampAt n ∘ φ`, with `clampAt n t = (−n) ∨ (t ∧ n)`.

## Main statements

* `memLp_two_v0_resampling`, `memLp_two_v1_resampling`,
  `memLp_two_noise0_resampling`, `memLp_two_noise1_resampling` — the `L²`
  clause "`(V⁽¹⁾, U⁽¹⁾) =ᵈ (V⁽⁰⁾, U⁽⁰⁾)`, in particular `V⁽¹⁾, U⁽¹⁾ ∈ L²`",
  and with them the four Cauchy–Schwarz products
  `integrable_noise0_mul_v0`, `integrable_noise0_mul_v1`,
  `integrable_noise1_mul_v0`, `integrable_noise1_mul_v1`;
* `integral_noise0_mul_v0` / `integral_noise1_mul_v1` — `E[U⁰V⁰] = 0` and
  `E[U¹V¹] = 0`;
* `integral_noise1_mul_v0_eq` — `E[U¹V⁰] = E[U⁰V¹]` (Lemma 2.6 (i));
* `integral_v1_mul_eq_inverseRegression_memLp` — Lemma 2.6 (iii) for `L²`
  test functions (see the route note below);
* `integral_noise0_mul_v1` — `E[U⁰V¹] = E[U⁰P(Y)] = Γ`;
* `replica_identity` — **(5.1)**,
  `2Γ = E[(φ(V⁰) − φ(V¹))(V⁰ − V¹)]`, with `integrable_replica_increment`;
* `integral_clamp_replica_eq` — **(5.2)**,
  `½E[(φₙ(V⁰) − φₙ(V¹))(V⁰ − V¹)] = E[φₙ(V)(V − F(φ(V)))]`;
* `clamp_increment_bounds` and `tendsto_clamp_replica` — **(5.3)**;
* `ae_clamp_insiderProfit` — Part IV's three-case pointwise statement
  `0 ≤ φₙ(V)(V − F(φ(V))) ↑ Π(V)` a.s.;
* `accounting_identity` — **v4 Proposition 5.1**;
* `noiseTraderLoss_eq_integral_insiderProfit`,
  `integrable_insiderProfit_of_isGammaSolution` — the equilibrium corollary,
  whose two hypotheses come free from v4 Lemma 2.4
  (`monotone_of_isGammaSolution`, `insiderProfit_nonneg`);
* `integral_insiderProfit_id` — the sanity oracle `E[Π(V)] = 1/2` at
  `φ = id`, which also de-vacuates the hypotheses of `accounting_identity`.

Auxiliary exports: the `clampAt` toolkit, `integral_resampling_swap`
(exchangeability in integral form) and `integral_pair_v0` / `integral_pair_v1`
(the two marginal transfers between `μ₃` and `γ ⊗ γ`).

## Route

Part I is transported onto `μ₃` exactly as in the paper. The paper's
"`(V⁽¹⁾, Y) =ᵈ (V⁽⁰⁾, Y)`" is `Resampling.resamplingMeasure_map_snd` /
`_map_fst`, and identifying that common marginal with
`Posterior.map_value_orderFlow` (the law of `(V, Y)` on `stdModel`) turns every
`(V⁽ⁱ⁾, Y)`-statement into a statement on `γ ⊗ γ`, where `U = Y − φ(V)` is
literally the second coordinate. That is `integral_pair_v0` /
`integral_pair_v1` / `memLp_pair_v0` / `memLp_pair_v1`, and it is what makes
`E[U⁰V⁰] = 0` a two-line independence computation.

The paper's tower-and-pull-out step `E[U⁰V¹] = E[U⁰P(Y)]` is clause (iii) of
Lemma 2.6. `Resampling.lean` proves that clause only for **bounded** Borel test
functions, whereas v4 §5 applies it to the unbounded `g(v, y) = y − φ(v)`; the
upgrade `integral_v1_mul_eq_inverseRegression_memLp` is proved here by lattice
truncation of `g` and dominated convergence against the Cauchy–Schwarz
majorants `|V¹g|` and `|P(Y)g|`. No `condExp` is used.

Part III departs from the paper in one place: v4 argues by monotone
convergence, using that `|φₙ(V⁰) − φₙ(V¹)|` increases to
`|φ(V⁰) − φ(V¹)|`. Since (5.1) already exhibits the limit
`(φ(V⁰) − φ(V¹))(V⁰ − V¹)` as **integrable** (it is a combination of the four
Cauchy–Schwarz products), dominated convergence applies directly, with that
limit as the majorant; the monotonicity of `n ↦ φₙ` is then needed only in the
one-sided form `clampAt_sub_le`. Part IV is the paper's three-case argument
verbatim (`clamp_mul_facts`), with the extended expectation `E[Π(V)] ∈ [0, ∞]`
realised as `∫⁻ v, ENNReal.ofReal (Π v) ∂γ`; monotone convergence there is
`lintegral_tendsto_of_tendsto_of_monotone`, and the finiteness it yields is
exactly `lintegral_ofReal_ne_top_iff_integrable`, i.e. `Π(V) ∈ L¹`.

## Hypotheses beyond the paper

None. Every statement carries only the paper's own hypotheses, plus the
explicit `Measurable φ` that v4 §2 carries as "Borel `φ`" throughout.

All section, equation and lemma numbers refer to arXiv:2607.23585 **v4**.
-/

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology

namespace KyleUniqueness

variable {φ : ℝ → ℝ}

/-! ## The lattice truncation -/

/-- The lattice truncation of v4 §5, Part II, as a function of the *value*:
`clampAt n t = (−n) ∨ (t ∧ n)`. The paper's `φₙ` is `clampAt n ∘ φ`. -/
noncomputable def clampAt (n : ℕ) (t : ℝ) : ℝ := max (-(n : ℝ)) (min t (n : ℝ))

lemma measurable_clampAt (n : ℕ) : Measurable (clampAt n) :=
  measurable_const.max (measurable_id.min measurable_const)

lemma clampAt_of_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : clampAt n t = min t (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [clampAt, max_eq_right (le_min (by linarith) (by linarith))]

lemma clampAt_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) : clampAt n t = max (-(n : ℝ)) t := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [clampAt, min_eq_left (by linarith)]

lemma clampAt_zero (n : ℕ) : clampAt n 0 = 0 := by
  rw [clampAt_of_nonneg n le_rfl, min_eq_left (Nat.cast_nonneg n)]

lemma monotone_clampAt (n : ℕ) : Monotone (clampAt n) := fun _ _ hab =>
  max_le_max le_rfl (min_le_min hab le_rfl)

lemma abs_clampAt_le (n : ℕ) (t : ℝ) : |clampAt n t| ≤ (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_le, clampAt]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma abs_clampAt_le_abs (n : ℕ) (t : ℝ) : |clampAt n t| ≤ |t| := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases le_total 0 t with ht | ht
  · rw [clampAt_of_nonneg n ht, abs_of_nonneg ht,
      abs_of_nonneg (le_min ht hn)]
    exact min_le_left _ _
  · rw [clampAt_of_nonpos n ht, abs_of_nonpos ht,
      abs_of_nonpos (max_le (by linarith) ht), neg_le_neg_iff]
    exact le_max_right _ _

lemma clampAt_eq_self {n : ℕ} {t : ℝ} (h : |t| ≤ (n : ℝ)) : clampAt n t = t := by
  rw [abs_le] at h
  rw [clampAt, min_eq_left h.2, max_eq_right h.1]

lemma tendsto_clampAt (t : ℝ) : Tendsto (fun n : ℕ => clampAt n t) atTop (𝓝 t) :=
  tendsto_atTop_of_eventually_const (i₀ := ⌈|t|⌉₊) fun _ hn =>
    clampAt_eq_self ((Nat.le_ceil _).trans (Nat.cast_le.2 hn))

/-- The truncation is `1`-Lipschitz, in the one-sided form used in Part III:
the truncated increment never exceeds the true increment. -/
lemma clampAt_sub_le (n : ℕ) {a b : ℝ} (hab : b ≤ a) :
    clampAt n a - clampAt n b ≤ a - b := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [clampAt, max_def, min_def]
  split_ifs <;> linarith

/-! ## Transfer between `μ₃` and the normalised model -/

/-- Measurability of the replica-exchange map `(v₀, v₁, y) ↦ (v₁, v₀, y)`. -/
private lemma measurable_exch' :
    Measurable fun q : ℝ × ℝ × ℝ => (q.2.1, q.1, q.2.2) :=
  measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)

/-- The shear `(v, u) ↦ (v, φ(v) + u)` realising `(V, Y)`. -/
private lemma measurable_shear (hφ : Measurable φ) :
    Measurable fun w : ℝ × ℝ => (w.1, φ w.1 + w.2) :=
  measurable_fst.prodMk ((hφ.comp measurable_fst).add measurable_snd)

private lemma measurable_pair_v0 :
    Measurable fun q : ℝ × ℝ × ℝ => (q.1, q.2.2) :=
  measurable_fst.prodMk measurable_snd.snd

private lemma measurable_pair_v1 :
    Measurable fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2) :=
  measurable_snd.fst.prodMk measurable_snd.snd

/-- **Exchangeability in integral form** (v4 Lemma 2.6 (i)). -/
theorem integral_resampling_swap (hφ : Measurable φ) {f : ℝ × ℝ × ℝ → ℝ}
    (hf : Measurable f) :
    ∫ q, f (q.2.1, q.1, q.2.2) ∂(resamplingMeasure φ)
      = ∫ q, f q ∂(resamplingMeasure φ) := by
  have h := integral_map (μ := resamplingMeasure φ) measurable_exch'.aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [resamplingMeasure_map_swap hφ] at h
  exact h.symm

/-- The `(V⁰, Y)`-marginal of `μ₃` is the law of `(V, Y)` on the normalised
model (v4 Lemma 2.6 (ii) composed with v4 Lemma 2.1). -/
private lemma map_pair_v0 (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2)) (resamplingMeasure φ)
      = Measure.map (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2))
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [resamplingMeasure_map_fst hφ, map_value_orderFlow hφ]
  rfl

/-- The `(V¹, Y)`-marginal of `μ₃` is the same law (v4 Lemma 2.6 (ii)). -/
private lemma map_pair_v1 (hφ : Measurable φ) :
    Measure.map (fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2)) (resamplingMeasure φ)
      = Measure.map (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2))
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [resamplingMeasure_map_snd hφ, map_value_orderFlow hφ]
  rfl

/-- Integrals of functions of `(V⁰, Y)` are computed on the normalised
model. -/
theorem integral_pair_v0 (hφ : Measurable φ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    ∫ q, f (q.1, q.2.2) ∂(resamplingMeasure φ)
      = ∫ w, f (w.1, φ w.1 + w.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h1 := integral_map (μ := resamplingMeasure φ) measurable_pair_v0.aemeasurable
    (f := f) hf.aestronglyMeasurable
  have h2 := integral_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (measurable_shear hφ).aemeasurable (f := f) hf.aestronglyMeasurable
  rw [map_pair_v0 hφ] at h1
  exact h1.symm.trans h2

/-- Integrals of functions of `(V¹, Y)` are computed on the normalised
model. -/
theorem integral_pair_v1 (hφ : Measurable φ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    ∫ q, f (q.2.1, q.2.2) ∂(resamplingMeasure φ)
      = ∫ w, f (w.1, φ w.1 + w.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h1 := integral_map (μ := resamplingMeasure φ) measurable_pair_v1.aemeasurable
    (f := f) hf.aestronglyMeasurable
  have h2 := integral_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (measurable_shear hφ).aemeasurable (f := f) hf.aestronglyMeasurable
  rw [map_pair_v1 hφ] at h1
  exact h1.symm.trans h2

/-- `L^p` transfer along the `(V⁰, Y)`-marginal. -/
private lemma memLp_pair_v0 (hφ : Measurable φ) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {p : ℝ≥0∞}
    (h : MemLp (fun w : ℝ × ℝ => f (w.1, φ w.1 + w.2)) p
      ((gaussianReal 0 1).prod (gaussianReal 0 1))) :
    MemLp (fun q : ℝ × ℝ × ℝ => f (q.1, q.2.2)) p (resamplingMeasure φ) := by
  have h2 : MemLp f p (Measure.map (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable
      (measurable_shear hφ).aemeasurable).mpr h
  rw [← map_pair_v0 hφ] at h2
  exact (memLp_map_measure_iff hf.aestronglyMeasurable
    measurable_pair_v0.aemeasurable).mp h2

/-- `L^p` transfer along the `(V¹, Y)`-marginal. -/
private lemma memLp_pair_v1 (hφ : Measurable φ) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {p : ℝ≥0∞}
    (h : MemLp (fun w : ℝ × ℝ => f (w.1, φ w.1 + w.2)) p
      ((gaussianReal 0 1).prod (gaussianReal 0 1))) :
    MemLp (fun q : ℝ × ℝ × ℝ => f (q.2.1, q.2.2)) p (resamplingMeasure φ) := by
  have h2 : MemLp f p (Measure.map (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable
      (measurable_shear hφ).aemeasurable).mpr h
  rw [← map_pair_v1 hφ] at h2
  exact (memLp_map_measure_iff hf.aestronglyMeasurable
    measurable_pair_v1.aemeasurable).mp h2

/-! ## `L²` facts under `μ₃` -/

/-- `V⁰ = V` is square-integrable under `μ₃` (it is standard normal). -/
theorem memLp_two_v0_resampling (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => q.1) 2 (resamplingMeasure φ) := by
  have h : MemLp id 2 (Measure.map (fun q : ℝ × ℝ × ℝ => q.1)
      (resamplingMeasure φ)) := by
    rw [resamplingMeasure_map_v0 hφ]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    measurable_fst.aemeasurable).mp h

/-- The replica `V¹` is square-integrable under `μ₃` (it is standard
normal). -/
theorem memLp_two_v1_resampling (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => q.2.1) 2 (resamplingMeasure φ) := by
  have h : MemLp id 2 (Measure.map (fun q : ℝ × ℝ × ℝ => q.2.1)
      (resamplingMeasure φ)) := by
    rw [resamplingMeasure_map_v1 hφ]
    simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    measurable_snd.fst.aemeasurable).mp h

/-- `U⁰ = Y − φ(V⁰) = U` is square-integrable under `μ₃`. -/
theorem memLp_two_noise0_resampling (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => q.2.2 - φ q.1) 2 (resamplingMeasure φ) := by
  have hf : Measurable fun r : ℝ × ℝ => r.2 - φ r.1 :=
    measurable_snd.sub (hφ.comp measurable_fst)
  have h2 : MemLp (fun w : ℝ × ℝ => w.2) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have h : MemLp id 2 (Measure.map (fun w : ℝ × ℝ => w.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
      rw [MeasureTheory.measurePreserving_snd.map_eq]
      simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      measurable_snd.aemeasurable).mp h
  have hU : MemLp (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2).2 - φ (w.1, φ w.1 + w.2).1) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have heq : (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2).2 - φ (w.1, φ w.1 + w.2).1)
        = fun w : ℝ × ℝ => w.2 := by
      funext w; simp
    rw [heq]; exact h2
  exact memLp_pair_v0 hφ (f := fun r : ℝ × ℝ => r.2 - φ r.1) hf hU

/-- `U¹ = Y − φ(V¹)` is square-integrable under `μ₃` — this is the content of
"`(V⁽¹⁾, U⁽¹⁾) =ᵈ (V⁽⁰⁾, U⁽⁰⁾)`, in particular `U⁽¹⁾ ∈ L²`" of v4 §5. -/
theorem memLp_two_noise1_resampling (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => q.2.2 - φ q.2.1) 2 (resamplingMeasure φ) := by
  have hf : Measurable fun r : ℝ × ℝ => r.2 - φ r.1 :=
    measurable_snd.sub (hφ.comp measurable_fst)
  have h2 : MemLp (fun w : ℝ × ℝ => w.2) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have h : MemLp id 2 (Measure.map (fun w : ℝ × ℝ => w.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
      rw [MeasureTheory.measurePreserving_snd.map_eq]
      simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      measurable_snd.aemeasurable).mp h
  have hU : MemLp (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2).2 - φ (w.1, φ w.1 + w.2).1) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have heq : (fun w : ℝ × ℝ => (w.1, φ w.1 + w.2).2 - φ (w.1, φ w.1 + w.2).1)
        = fun w : ℝ × ℝ => w.2 := by
      funext w; simp
    rw [heq]; exact h2
  exact memLp_pair_v1 hφ (f := fun r : ℝ × ℝ => r.2 - φ r.1) hf hU

/-- `P(Y) ∈ L²(μ₃)` (v4 Lemma 2.2, transported to the resampling space). -/
theorem memLp_two_inverseRegression_resampling (hφ : Measurable φ) :
    MemLp (fun q : ℝ × ℝ × ℝ => inverseRegression φ q.2.2) 2
      (resamplingMeasure φ) := by
  have hf : Measurable fun r : ℝ × ℝ => inverseRegression φ r.2 :=
    (measurable_inverseRegression hφ).comp measurable_snd
  exact memLp_pair_v0 hφ (f := fun r : ℝ × ℝ => inverseRegression φ r.2) hf
    (lemma22_memLp_two hφ)

/-! ## The four products of v4 §5 -/

/-- `U⁰·V⁰ ∈ L¹` (Cauchy–Schwarz). -/
theorem integrable_noise0_mul_v0 (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => (q.2.2 - φ q.1) * q.1) (resamplingMeasure φ) :=
  (memLp_two_noise0_resampling hφ).integrable_mul (memLp_two_v0_resampling hφ)

/-- `U⁰·V¹ ∈ L¹` (Cauchy–Schwarz). -/
theorem integrable_noise0_mul_v1 (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => (q.2.2 - φ q.1) * q.2.1) (resamplingMeasure φ) :=
  (memLp_two_noise0_resampling hφ).integrable_mul (memLp_two_v1_resampling hφ)

/-- `U¹·V⁰ ∈ L¹` (Cauchy–Schwarz). -/
theorem integrable_noise1_mul_v0 (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => (q.2.2 - φ q.2.1) * q.1) (resamplingMeasure φ) :=
  (memLp_two_noise1_resampling hφ).integrable_mul (memLp_two_v0_resampling hφ)

/-- `U¹·V¹ ∈ L¹` (Cauchy–Schwarz). -/
theorem integrable_noise1_mul_v1 (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => (q.2.2 - φ q.2.1) * q.2.1) (resamplingMeasure φ) :=
  (memLp_two_noise1_resampling hφ).integrable_mul (memLp_two_v1_resampling hφ)

/-- **v4 §5, Part I**: `E[U⁰V⁰] = 0`, because `U⁰ = U` and `V⁰ = V` are
independent and centred. -/
theorem integral_noise0_mul_v0 (hφ : Measurable φ) :
    ∫ q, (q.2.2 - φ q.1) * q.1 ∂(resamplingMeasure φ) = 0 := by
  have hf : Measurable fun r : ℝ × ℝ => (r.2 - φ r.1) * r.1 :=
    (measurable_snd.sub (hφ.comp measurable_fst)).mul measurable_fst
  calc ∫ q, (q.2.2 - φ q.1) * q.1 ∂(resamplingMeasure φ)
      = ∫ w, ((φ w.1 + w.2) - φ w.1) * w.1
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := integral_pair_v0 hφ hf
    _ = ∫ w : ℝ × ℝ, w.1 * w.2 ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
        integral_congr_ae (ae_of_all _ fun w => by ring)
    _ = 0 := by
        rw [integral_prod_mul (f := fun x : ℝ => x) (g := fun y : ℝ => y),
          integral_id_gaussianReal, mul_zero]

/-- **v4 §5, Part I**: `E[U¹V¹] = E[U⁰V⁰] = 0`, by exchangeability. -/
theorem integral_noise1_mul_v1 (hφ : Measurable φ) :
    ∫ q, (q.2.2 - φ q.2.1) * q.2.1 ∂(resamplingMeasure φ) = 0 := by
  have hf : Measurable fun q : ℝ × ℝ × ℝ => (q.2.2 - φ q.1) * q.1 :=
    (measurable_snd.snd.sub (hφ.comp measurable_fst)).mul measurable_fst
  exact (integral_resampling_swap hφ hf).trans (integral_noise0_mul_v0 hφ)

/-- **v4 §5, Part I**, from Lemma 2.6 (i): `E[U¹V⁰] = E[U⁰V¹]`. -/
theorem integral_noise1_mul_v0_eq (hφ : Measurable φ) :
    ∫ q, (q.2.2 - φ q.2.1) * q.1 ∂(resamplingMeasure φ)
      = ∫ q, (q.2.2 - φ q.1) * q.2.1 ∂(resamplingMeasure φ) := by
  have hf : Measurable fun q : ℝ × ℝ × ℝ => (q.2.2 - φ q.1) * q.2.1 :=
    (measurable_snd.snd.sub (hφ.comp measurable_fst)).mul measurable_snd.fst
  exact integral_resampling_swap hφ hf

/-! ## Clause (iii) of v4 Lemma 2.6 for `L²` test functions -/

/-- **v4 Lemma 2.6 (iii), `L²` form.** `Resampling.lean` proves
`E[V¹ g(V⁰, Y)] = E[P(Y) g(V⁰, Y)]` only for *bounded* Borel `g`; v4 §5
applies it to `g(v, y) = y − φ(v)`, which is unbounded. Lattice truncation
plus dominated convergence (with the Cauchy–Schwarz majorants
`|V¹ g|`, `|P(Y) g|`) upgrades the clause to every Borel `g` with
`g(V⁰, Y) ∈ L²`. -/
theorem integral_v1_mul_eq_inverseRegression_memLp (hφ : Measurable φ)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (hg2 : MemLp (fun q : ℝ × ℝ × ℝ => g (q.1, q.2.2)) 2 (resamplingMeasure φ)) :
    ∫ q, q.2.1 * g (q.1, q.2.2) ∂(resamplingMeasure φ)
      = ∫ q, inverseRegression φ q.2.2 * g (q.1, q.2.2)
          ∂(resamplingMeasure φ) := by
  have hgm : Measurable fun q : ℝ × ℝ × ℝ => g (q.1, q.2.2) := hg.comp measurable_pair_v0
  have hL : Integrable (fun q : ℝ × ℝ × ℝ => q.2.1 * g (q.1, q.2.2))
      (resamplingMeasure φ) :=
    (memLp_two_v1_resampling hφ).integrable_mul hg2
  have hR : Integrable
      (fun q : ℝ × ℝ × ℝ => inverseRegression φ q.2.2 * g (q.1, q.2.2))
      (resamplingMeasure φ) :=
    (memLp_two_inverseRegression_resampling hφ).integrable_mul hg2
  have hstep : ∀ n : ℕ,
      ∫ q, q.2.1 * clampAt n (g (q.1, q.2.2)) ∂(resamplingMeasure φ)
        = ∫ q, inverseRegression φ q.2.2 * clampAt n (g (q.1, q.2.2))
            ∂(resamplingMeasure φ) := fun n =>
    integral_v1_mul_eq_inverseRegression hφ ((measurable_clampAt n).comp hg)
      (C := (n : ℝ)) (fun r => abs_clampAt_le n (g r))
  have hlimL : Tendsto
      (fun n : ℕ => ∫ q, q.2.1 * clampAt n (g (q.1, q.2.2))
        ∂(resamplingMeasure φ)) atTop
      (𝓝 (∫ q, q.2.1 * g (q.1, q.2.2) ∂(resamplingMeasure φ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun q : ℝ × ℝ × ℝ => |q.2.1 * g (q.1, q.2.2)|) (fun n => ?_) hL.abs
      (fun n => ?_) ?_
    · exact (measurable_snd.fst.mul
        ((measurable_clampAt n).comp hgm)).aestronglyMeasurable
    · refine ae_of_all _ fun q => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_clampAt_le_abs n _) (abs_nonneg _)
    · exact ae_of_all _ fun q =>
        (tendsto_clampAt (g (q.1, q.2.2))).const_mul q.2.1
  have hlimR : Tendsto
      (fun n : ℕ => ∫ q, inverseRegression φ q.2.2 * clampAt n (g (q.1, q.2.2))
        ∂(resamplingMeasure φ)) atTop
      (𝓝 (∫ q, inverseRegression φ q.2.2 * g (q.1, q.2.2)
        ∂(resamplingMeasure φ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun q : ℝ × ℝ × ℝ => |inverseRegression φ q.2.2 * g (q.1, q.2.2)|)
      (fun n => ?_) hR.abs (fun n => ?_) ?_
    · exact (((measurable_inverseRegression hφ).comp measurable_snd.snd).mul
        ((measurable_clampAt n).comp hgm)).aestronglyMeasurable
    · refine ae_of_all _ fun q => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_clampAt_le_abs n _) (abs_nonneg _)
    · exact ae_of_all _ fun q =>
        (tendsto_clampAt (g (q.1, q.2.2))).const_mul (inverseRegression φ q.2.2)
  refine tendsto_nhds_unique hlimL ?_
  simp only [hstep]
  exact hlimR

/-- **v4 §5, Part I**, the tower-and-pull-out step: `E[U⁰V¹] = E[U⁰P(Y)] = Γ`. -/
theorem integral_noise0_mul_v1 (hφ : Measurable φ) :
    ∫ q, (q.2.2 - φ q.1) * q.2.1 ∂(resamplingMeasure φ) = noiseTraderLoss φ := by
  have hg : Measurable fun r : ℝ × ℝ => r.2 - φ r.1 :=
    measurable_snd.sub (hφ.comp measurable_fst)
  have hf : Measurable fun r : ℝ × ℝ => inverseRegression φ r.2 * (r.2 - φ r.1) :=
    ((measurable_inverseRegression hφ).comp measurable_snd).mul hg
  have key := integral_v1_mul_eq_inverseRegression_memLp hφ hg
    (memLp_two_noise0_resampling hφ)
  calc ∫ q, (q.2.2 - φ q.1) * q.2.1 ∂(resamplingMeasure φ)
      = ∫ q, q.2.1 * (q.2.2 - φ q.1) ∂(resamplingMeasure φ) :=
        integral_congr_ae (ae_of_all _ fun q => mul_comm _ _)
    _ = ∫ q, inverseRegression φ q.2.2 * (q.2.2 - φ q.1)
          ∂(resamplingMeasure φ) := key
    _ = ∫ w, inverseRegression φ (φ w.1 + w.2) * ((φ w.1 + w.2) - φ w.1)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := integral_pair_v0 hφ hf
    _ = ∫ w : ℝ × ℝ, w.2 * inverseRegression φ (φ w.1 + w.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
        integral_congr_ae (ae_of_all _ fun w => by ring)
    _ = noiseTraderLoss φ := rfl

/-! ## The replica identity (5.1) -/

/-- The integrand of v4 (5.1) is integrable: it is the combination
`(U¹ − U⁰)(V⁰ − V¹)` of the four Cauchy–Schwarz products. -/
theorem integrable_replica_increment (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => (φ q.1 - φ q.2.1) * (q.1 - q.2.1))
      (resamplingMeasure φ) := by
  have hA : Integrable (fun q : ℝ × ℝ × ℝ =>
      (q.2.2 - φ q.2.1) * q.1 + (q.2.2 - φ q.1) * q.2.1) (resamplingMeasure φ) :=
    (integrable_noise1_mul_v0 hφ).add (integrable_noise0_mul_v1 hφ)
  have hB : Integrable (fun q : ℝ × ℝ × ℝ =>
      (q.2.2 - φ q.2.1) * q.2.1 + (q.2.2 - φ q.1) * q.1) (resamplingMeasure φ) :=
    (integrable_noise1_mul_v1 hφ).add (integrable_noise0_mul_v0 hφ)
  have hsum : Integrable (fun q : ℝ × ℝ × ℝ =>
      ((q.2.2 - φ q.2.1) * q.1 + (q.2.2 - φ q.1) * q.2.1)
        - ((q.2.2 - φ q.2.1) * q.2.1 + (q.2.2 - φ q.1) * q.1))
      (resamplingMeasure φ) := hA.sub hB
  refine hsum.congr (ae_of_all _ fun q => ?_)
  ring

/-- **v4 eq. (5.1)** (symmetric representation of `Γ`):
`2Γ = E[(φ(V⁰) − φ(V¹))(V⁰ − V¹)]`. -/
theorem replica_identity (hφ : Measurable φ) :
    2 * noiseTraderLoss φ
      = ∫ q, (φ q.1 - φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ) := by
  have hA : Integrable (fun q : ℝ × ℝ × ℝ =>
      (q.2.2 - φ q.2.1) * q.1 + (q.2.2 - φ q.1) * q.2.1) (resamplingMeasure φ) :=
    (integrable_noise1_mul_v0 hφ).add (integrable_noise0_mul_v1 hφ)
  have hB : Integrable (fun q : ℝ × ℝ × ℝ =>
      (q.2.2 - φ q.2.1) * q.2.1 + (q.2.2 - φ q.1) * q.1) (resamplingMeasure φ) :=
    (integrable_noise1_mul_v1 hφ).add (integrable_noise0_mul_v0 hφ)
  have hexp : ∫ q, (φ q.1 - φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
      = ((∫ q, (q.2.2 - φ q.2.1) * q.1 ∂(resamplingMeasure φ))
          + ∫ q, (q.2.2 - φ q.1) * q.2.1 ∂(resamplingMeasure φ))
        - ((∫ q, (q.2.2 - φ q.2.1) * q.2.1 ∂(resamplingMeasure φ))
          + ∫ q, (q.2.2 - φ q.1) * q.1 ∂(resamplingMeasure φ)) := by
    calc ∫ q, (φ q.1 - φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
        = ∫ q, (((q.2.2 - φ q.2.1) * q.1 + (q.2.2 - φ q.1) * q.2.1)
            - ((q.2.2 - φ q.2.1) * q.2.1 + (q.2.2 - φ q.1) * q.1))
            ∂(resamplingMeasure φ) :=
          integral_congr_ae (ae_of_all _ fun q => by ring)
      _ = (∫ q, ((q.2.2 - φ q.2.1) * q.1 + (q.2.2 - φ q.1) * q.2.1)
              ∂(resamplingMeasure φ))
            - ∫ q, ((q.2.2 - φ q.2.1) * q.2.1 + (q.2.2 - φ q.1) * q.1)
              ∂(resamplingMeasure φ) := integral_sub hA hB
      _ = _ := by
          rw [integral_add (integrable_noise1_mul_v0 hφ) (integrable_noise0_mul_v1 hφ),
            integral_add (integrable_noise1_mul_v1 hφ) (integrable_noise0_mul_v0 hφ)]
  rw [hexp, integral_noise1_mul_v0_eq hφ, integral_noise0_mul_v1 hφ,
    integral_noise1_mul_v1 hφ, integral_noise0_mul_v0 hφ]
  ring

/-! ## Truncation: v4 eq. (5.2) -/

/-- Integrals of functions of `V⁰` alone are computed against the prior. -/
private lemma integral_v0_marginal (hφ : Measurable φ) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ q, g q.1 ∂(resamplingMeasure φ) = ∫ v, g v ∂(gaussianReal 0 1) := by
  have h := integral_map (μ := resamplingMeasure φ) measurable_fst.aemeasurable
    (f := g) hg.aestronglyMeasurable
  rw [resamplingMeasure_map_v0 hφ] at h
  exact h.symm

private lemma integrable_v0_sub_v1 (hφ : Measurable φ) :
    Integrable (fun q : ℝ × ℝ × ℝ => q.1 - q.2.1) (resamplingMeasure φ) :=
  (integrable_v0_resampling hφ).sub (integrable_v1_resampling hφ)

/-- **v4 eq. (5.2)**: with the bounded truncation `φₙ = clampAt n ∘ φ`, the
symmetric increment collapses to an integral against the prior:
`½E[(φₙ(V⁰) − φₙ(V¹))(V⁰ − V¹)] = E[φₙ(V)(V − F(φ(V)))]`. -/
theorem integral_clamp_replica_eq (hφ : Measurable φ) (n : ℕ) :
    (1 / 2 : ℝ) * ∫ q, (clampAt n (φ q.1) - clampAt n (φ q.2.1)) * (q.1 - q.2.1)
        ∂(resamplingMeasure φ)
      = ∫ v, clampAt n (φ v) * (v - gaussianSmoothing φ (φ v))
          ∂(gaussianReal 0 1) := by
  have hk : Measurable fun v => clampAt n (φ v) := (measurable_clampAt n).comp hφ
  have hkb : ∀ᵐ q ∂(resamplingMeasure φ), ‖clampAt n (φ q.1)‖ ≤ (n : ℝ) :=
    ae_of_all _ fun q => by
      rw [Real.norm_eq_abs]; exact abs_clampAt_le n (φ q.1)
  have hkb' : ∀ᵐ q ∂(resamplingMeasure φ), ‖clampAt n (φ q.2.1)‖ ≤ (n : ℝ) :=
    ae_of_all _ fun q => by
      rw [Real.norm_eq_abs]; exact abs_clampAt_le n (φ q.2.1)
  have hA : Integrable
      (fun q : ℝ × ℝ × ℝ => clampAt n (φ q.1) * (q.1 - q.2.1))
      (resamplingMeasure φ) :=
    (integrable_v0_sub_v1 hφ).bdd_mul (hk.comp measurable_fst).aestronglyMeasurable hkb
  have hB : Integrable
      (fun q : ℝ × ℝ × ℝ => clampAt n (φ q.2.1) * (q.1 - q.2.1))
      (resamplingMeasure φ) :=
    (integrable_v0_sub_v1 hφ).bdd_mul
      (hk.comp measurable_snd.fst).aestronglyMeasurable hkb'
  -- the two halves of the increment have opposite integrals, by exchangeability
  have hswap : ∫ q, clampAt n (φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
      = -∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ) := by
    have hf : Measurable fun q : ℝ × ℝ × ℝ => clampAt n (φ q.1) * (q.2.1 - q.1) :=
      (hk.comp measurable_fst).mul (measurable_snd.fst.sub measurable_fst)
    calc ∫ q, clampAt n (φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
        = ∫ q, clampAt n (φ q.1) * (q.2.1 - q.1) ∂(resamplingMeasure φ) :=
          integral_resampling_swap hφ hf
      _ = ∫ q, -(clampAt n (φ q.1) * (q.1 - q.2.1)) ∂(resamplingMeasure φ) :=
          integral_congr_ae (ae_of_all _ fun q => by ring)
      _ = -∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ) :=
          integral_neg _
  -- the surviving half splits into the two marginal integrals
  have hv0 : Integrable (fun v : ℝ => clampAt n (φ v) * v) (gaussianReal 0 1) := by
    have h : Integrable (fun v : ℝ => clampAt n (φ v) * v) (gaussianReal 0 1) :=
      (integrable_id_gaussianReal 0 1).bdd_mul hk.aestronglyMeasurable
        (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact abs_clampAt_le n (φ v))
    exact h
  have hvF : Integrable
      (fun v : ℝ => gaussianSmoothing φ (φ v) * clampAt n (φ v)) (gaussianReal 0 1) :=
    (integrable_gaussianSmoothing_comp hφ).mul_bdd hk.aestronglyMeasurable
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact abs_clampAt_le n (φ v))
  have hhalf : ∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
      = ∫ v, clampAt n (φ v) * (v - gaussianSmoothing φ (φ v))
          ∂(gaussianReal 0 1) := by
    have hsplit : ∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
        = (∫ q, clampAt n (φ q.1) * q.1 ∂(resamplingMeasure φ))
          - ∫ q, clampAt n (φ q.1) * q.2.1 ∂(resamplingMeasure φ) := by
      have h1 : Integrable (fun q : ℝ × ℝ × ℝ => clampAt n (φ q.1) * q.1)
          (resamplingMeasure φ) :=
        (integrable_v0_resampling hφ).bdd_mul
          (hk.comp measurable_fst).aestronglyMeasurable hkb
      have h2 : Integrable (fun q : ℝ × ℝ × ℝ => clampAt n (φ q.1) * q.2.1)
          (resamplingMeasure φ) :=
        (integrable_v1_resampling hφ).bdd_mul
          (hk.comp measurable_fst).aestronglyMeasurable hkb
      calc ∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ)
          = ∫ q, (clampAt n (φ q.1) * q.1 - clampAt n (φ q.1) * q.2.1)
              ∂(resamplingMeasure φ) :=
            integral_congr_ae (ae_of_all _ fun q => by ring)
        _ = _ := integral_sub h1 h2
    have hfst : ∫ q, clampAt n (φ q.1) * q.1 ∂(resamplingMeasure φ)
        = ∫ v, clampAt n (φ v) * v ∂(gaussianReal 0 1) :=
      integral_v0_marginal hφ (g := fun v => clampAt n (φ v) * v) (hk.mul measurable_id)
    have hsnd : ∫ q, clampAt n (φ q.1) * q.2.1 ∂(resamplingMeasure φ)
        = ∫ v, gaussianSmoothing φ (φ v) * clampAt n (φ v) ∂(gaussianReal 0 1) := by
      calc ∫ q, clampAt n (φ q.1) * q.2.1 ∂(resamplingMeasure φ)
          = ∫ q, q.2.1 * clampAt n (φ q.1) ∂(resamplingMeasure φ) :=
            integral_congr_ae (ae_of_all _ fun q => mul_comm _ _)
        _ = _ := integral_v1_mul_comp_eq_gaussianSmoothing hφ (measurable_clampAt n)
              (C := (n : ℝ)) (fun x => abs_clampAt_le n x)
    rw [hsplit, hfst, hsnd, ← integral_sub hv0 hvF]
    exact integral_congr_ae (ae_of_all _ fun v => by ring)
  have hdiff : ∫ q, (clampAt n (φ q.1) - clampAt n (φ q.2.1)) * (q.1 - q.2.1)
      ∂(resamplingMeasure φ)
      = 2 * ∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ) := by
    calc ∫ q, (clampAt n (φ q.1) - clampAt n (φ q.2.1)) * (q.1 - q.2.1)
          ∂(resamplingMeasure φ)
        = ∫ q, (clampAt n (φ q.1) * (q.1 - q.2.1)
            - clampAt n (φ q.2.1) * (q.1 - q.2.1)) ∂(resamplingMeasure φ) :=
          integral_congr_ae (ae_of_all _ fun q => by ring)
      _ = (∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ))
            - ∫ q, clampAt n (φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ) :=
          integral_sub hA hB
      _ = 2 * ∫ q, clampAt n (φ q.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ) := by
          rw [hswap]; ring
  rw [hdiff, ← hhalf]
  ring

/-! ## Part III: the first monotone limit, v4 eq. (5.3) -/

/-- The supermodularity increment of v4 Part III: for a nondecreasing `φ` the
truncated increment is nonnegative and dominated by the untruncated one. -/
theorem clamp_increment_bounds (hmono : Monotone φ) (n : ℕ) (x y : ℝ) :
    0 ≤ (clampAt n (φ x) - clampAt n (φ y)) * (x - y) ∧
      (clampAt n (φ x) - clampAt n (φ y)) * (x - y) ≤ (φ x - φ y) * (x - y) := by
  rcases le_total y x with h | h
  · have hab : φ y ≤ φ x := hmono h
    have h1 : 0 ≤ clampAt n (φ x) - clampAt n (φ y) :=
      sub_nonneg.2 (monotone_clampAt n hab)
    have h2 : clampAt n (φ x) - clampAt n (φ y) ≤ φ x - φ y := clampAt_sub_le n hab
    have hxy : 0 ≤ x - y := sub_nonneg.2 h
    exact ⟨mul_nonneg h1 hxy, mul_le_mul_of_nonneg_right h2 hxy⟩
  · have hab : φ x ≤ φ y := hmono h
    have h1 : 0 ≤ clampAt n (φ y) - clampAt n (φ x) :=
      sub_nonneg.2 (monotone_clampAt n hab)
    have h2 : clampAt n (φ y) - clampAt n (φ x) ≤ φ y - φ x := clampAt_sub_le n hab
    have hxy : 0 ≤ y - x := sub_nonneg.2 h
    exact ⟨by nlinarith, by nlinarith⟩

/-- **v4 eq. (5.3)**: the truncated symmetric increments converge to `Γ`.
(The paper argues by monotone convergence; here (5.1) already supplies the
integrable majorant `(φ(V⁰) − φ(V¹))(V⁰ − V¹)`, so dominated convergence
applies directly.) -/
theorem tendsto_clamp_replica (hφ : Measurable φ) (hmono : Monotone φ) :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ) *
        ∫ q, (clampAt n (φ q.1) - clampAt n (φ q.2.1)) * (q.1 - q.2.1)
          ∂(resamplingMeasure φ)) atTop (𝓝 (noiseTraderLoss φ)) := by
  have hDCT : Tendsto (fun n : ℕ =>
      ∫ q, (clampAt n (φ q.1) - clampAt n (φ q.2.1)) * (q.1 - q.2.1)
        ∂(resamplingMeasure φ)) atTop
      (𝓝 (∫ q, (φ q.1 - φ q.2.1) * (q.1 - q.2.1) ∂(resamplingMeasure φ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun q : ℝ × ℝ × ℝ => (φ q.1 - φ q.2.1) * (q.1 - q.2.1)) (fun n => ?_)
      (integrable_replica_increment hφ) (fun n => ?_) ?_
    · exact ((((measurable_clampAt n).comp hφ).comp measurable_fst).sub
        (((measurable_clampAt n).comp hφ).comp measurable_snd.fst)).mul
        (measurable_fst.sub measurable_snd.fst) |>.aestronglyMeasurable
    · refine ae_of_all _ fun q => ?_
      obtain ⟨hpos, hle⟩ := clamp_increment_bounds hmono n q.1 q.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      exact hle
    · refine ae_of_all _ fun q => ?_
      exact ((tendsto_clampAt (φ q.1)).sub (tendsto_clampAt (φ q.2.1))).mul_const _
  have h2 := hDCT.const_mul (1 / 2 : ℝ)
  rw [← replica_identity hφ] at h2
  have hval : (1 / 2 : ℝ) * (2 * noiseTraderLoss φ) = noiseTraderLoss φ := by ring
  rw [hval] at h2
  exact h2

/-! ## Part IV: the matching monotone limit, and the accounting identity -/

/-- The elementary three-case argument of v4 Part IV: if `s·t ≥ 0`, then the
truncations `clampAt n s` multiplied by `t` increase from `0` to `s·t`. -/
private lemma clamp_mul_facts {s t : ℝ} (h : 0 ≤ s * t) :
    (∀ n : ℕ, 0 ≤ clampAt n s * t) ∧ Monotone (fun n : ℕ => clampAt n s * t) := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have ht : t ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_neg_of_neg_of_pos hs hc]
    have hc : ∀ n : ℕ, clampAt n s ≤ 0 := fun n => by
      rw [clampAt_of_nonpos n hs.le]
      exact max_le (neg_nonpos.2 (Nat.cast_nonneg n)) hs.le
    refine ⟨fun n => mul_nonneg_of_nonpos_of_nonpos (hc n) ht, fun m n hmn => ?_⟩
    have hle : clampAt n s ≤ clampAt m s := by
      rw [clampAt_of_nonpos m hs.le, clampAt_of_nonpos n hs.le]
      exact max_le_max (neg_le_neg (Nat.cast_le.2 hmn)) le_rfl
    exact mul_le_mul_of_nonpos_right hle ht
  · subst hs
    refine ⟨fun n => ?_, fun m n _ => ?_⟩ <;>
      simp only [clampAt_zero, zero_mul, le_refl]
  · have ht : 0 ≤ t := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_neg_of_pos_of_neg hs hc]
    have hc : ∀ n : ℕ, clampAt n s = min s (n : ℝ) := fun n => clampAt_of_nonneg n hs.le
    refine ⟨fun n => ?_, fun m n hmn => ?_⟩
    · rw [hc n]
      exact mul_nonneg (le_min hs.le (Nat.cast_nonneg n)) ht
    · simp only [hc]
      exact mul_le_mul_of_nonneg_right (min_le_min le_rfl (Nat.cast_le.2 hmn)) ht

/-- **v4 §5, Part IV**, the pointwise statement: on a full event the
truncated integrands of (5.2) increase from `0` to `Π(V)`. -/
theorem ae_clamp_insiderProfit (hPi : ∀ᵐ v ∂(gaussianReal 0 1), 0 ≤ insiderProfit φ v) :
    ∀ᵐ v ∂(gaussianReal 0 1),
      (∀ n : ℕ, 0 ≤ clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)))
        ∧ Monotone (fun n : ℕ => clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)))
        ∧ Tendsto (fun n : ℕ => clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)))
            atTop (𝓝 (insiderProfit φ v)) := by
  filter_upwards [hPi] with v hv
  rw [insiderProfit_apply] at hv
  obtain ⟨h1, h2⟩ := clamp_mul_facts hv
  refine ⟨h1, h2, ?_⟩
  rw [insiderProfit_apply]
  exact (tendsto_clampAt (φ v)).mul_const _

/-- **v4 Proposition 5.1 (accounting identity).** If `φ` is nondecreasing and
the insider's attained profit `Π(V) = φ(V)(V − F(φ(V)))` is almost surely
nonnegative, then `Π(V) ∈ L¹` and `Γ = E[Π(V)]`.

No integrability assumption on `φ(V)` or on `Π(V)` is made: the lattice
truncation (5.2), the dominated limit (5.3) and the monotone limit of Part IV
supply it. -/
theorem accounting_identity (hφ : Measurable φ) (hmono : Monotone φ)
    (hPi : ∀ᵐ v ∂(gaussianReal 0 1), 0 ≤ insiderProfit φ v) :
    Integrable (insiderProfit φ) (gaussianReal 0 1) ∧
      noiseTraderLoss φ = ∫ v, insiderProfit φ v ∂(gaussianReal 0 1) := by
  have hk : ∀ n : ℕ, Measurable
      fun v => clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)) := fun n =>
    ((measurable_clampAt n).comp hφ).mul (measurable_id.sub
      ((continuous_gaussianSmoothing hφ).measurable.comp hφ))
  have hmPi : Measurable (insiderProfit φ) := measurable_insiderProfit hφ
  have hfacts := ae_clamp_insiderProfit (φ := φ) hPi
  have hnn : ∀ n : ℕ, 0 ≤ᵐ[gaussianReal 0 1]
      fun v => clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)) := fun n => by
    filter_upwards [hfacts] with v hv using hv.1 n
  have hgint : ∀ n : ℕ, Integrable
      (fun v => clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)))
      (gaussianReal 0 1) := fun n => by
    have hd : Integrable (fun v : ℝ => v - gaussianSmoothing φ (φ v))
        (gaussianReal 0 1) :=
      (integrable_id_gaussianReal 0 1).sub (integrable_gaussianSmoothing_comp hφ)
    exact hd.bdd_mul (((measurable_clampAt n).comp hφ)).aestronglyMeasurable
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact abs_clampAt_le n (φ v))
  -- the real integrals converge to `Γ` by (5.2) and (5.3)
  have hΓ : Tendsto (fun n : ℕ =>
      ∫ v, clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)) ∂(gaussianReal 0 1))
      atTop (𝓝 (noiseTraderLoss φ)) := by
    have h := tendsto_clamp_replica hφ hmono
    simpa only [integral_clamp_replica_eq hφ] using h
  -- the same sequence computes the extended expectation of `Π(V)`
  have hlin : Tendsto (fun n : ℕ => ∫⁻ v,
      ENNReal.ofReal (clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)))
        ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫⁻ v, ENNReal.ofReal (insiderProfit φ v) ∂(gaussianReal 0 1))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hk n).ennreal_ofReal.aemeasurable) ?_ ?_
    · filter_upwards [hfacts] with v hv
      exact fun m n hmn => ENNReal.ofReal_le_ofReal (hv.2.1 hmn)
    · filter_upwards [hfacts] with v hv
      exact ENNReal.tendsto_ofReal hv.2.2
  have hlin2 : Tendsto (fun n : ℕ => ENNReal.ofReal
      (∫ v, clampAt n (φ v) * (v - gaussianSmoothing φ (φ v)) ∂(gaussianReal 0 1)))
      atTop (𝓝 (∫⁻ v, ENNReal.ofReal (insiderProfit φ v) ∂(gaussianReal 0 1))) := by
    refine hlin.congr fun n => ?_
    exact ofReal_integral_eq_lintegral_ofReal (hgint n) (hnn n) |>.symm
  have hval : ∫⁻ v, ENNReal.ofReal (insiderProfit φ v) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (noiseTraderLoss φ) :=
    tendsto_nhds_unique hlin2 (ENNReal.tendsto_ofReal hΓ)
  have hint : Integrable (insiderProfit φ) (gaussianReal 0 1) :=
    (lintegral_ofReal_ne_top_iff_integrable hmPi.aestronglyMeasurable hPi).mp
      (by rw [hval]; exact ENNReal.ofReal_ne_top)
  have hΓnn : 0 ≤ noiseTraderLoss φ :=
    ge_of_tendsto' hΓ fun n => integral_nonneg_of_ae (hnn n)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hPi hmPi.aestronglyMeasurable, hval,
    ENNReal.toReal_ofReal hΓnn]

/-! ## The equilibrium corollary -/

/-- The insider's profit is integrable at any pointwise maximiser (v4 §5,
applied through v4 Lemma 2.4: such a `φ` is nondecreasing and `Π ≥ 0`). -/
theorem integrable_insiderProfit_of_isGammaSolution (h : IsGammaSolution 0 φ) :
    Integrable (insiderProfit φ) (gaussianReal 0 1) :=
  (accounting_identity h.1 (monotone_of_isGammaSolution h)
    (ae_of_all _ (insiderProfit_nonneg h))).1

/-- **v4 Proposition 5.1 at a pointwise maximiser**: the noise traders' loss
equals the insider's ex ante expected profit, `Γ = E[Π(V)]`. Both hypotheses
of Proposition 5.1 come free from v4 Lemma 2.4. -/
theorem noiseTraderLoss_eq_integral_insiderProfit (h : IsGammaSolution 0 φ) :
    noiseTraderLoss φ = ∫ v, insiderProfit φ v ∂(gaussianReal 0 1) :=
  (accounting_identity h.1 (monotone_of_isGammaSolution h)
    (ae_of_all _ (insiderProfit_nonneg h))).2

/-! ## Sanity oracle -/

/-- Sanity oracle: at the Kyle equilibrium strategy `φ = id` the accounting
identity reads `E[Π(V)] = E[V²/2] = Γ = 1/2` (`insiderProfit_id`,
`noiseTraderLoss_id`). Since `id` satisfies all three hypotheses of
`accounting_identity`, this also witnesses that they are not vacuous. -/
theorem integral_insiderProfit_id :
    ∫ v : ℝ, insiderProfit id v ∂(gaussianReal 0 1) = 1 / 2 := by
  have h := accounting_identity (φ := id) measurable_id monotone_id
    (ae_of_all _ fun v => by simp only [insiderProfit_id]; positivity)
  rw [← h.2, noiseTraderLoss_id]

end KyleUniqueness
