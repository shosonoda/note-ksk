
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Topology.Algebra.InfiniteSum

/-!
# Lebesgue integral theory: counterexamples

This file collects a few standard counterexamples showing that the hypotheses of the usual
convergence theorems and Fubini/Tonelli cannot be dropped.

The examples are chosen to be *Lean-friendly*: we work mostly on `ℕ` with the counting measure,
so integrals reduce to (absolutely convergent) series, and one can compute them using
`MeasureTheory.integral_countable'`.

Main examples
* `spike n = δ_n` on `(ℕ, Measure.count)`: `spike n k → 0` pointwise, but `∫ spike n = 1` for all `n`.
  This breaks any "naive" version of convergence theorems if you drop key hypotheses.
* A discrete Fubini counterexample on `ℕ × ℕ`: iterated integrals exist but depend on the order.
-/

noncomputable section

open scoped BigOperators
open Filter MeasureTheory

namespace LebesgueIntegralCounterexamples

/-- A single spike at `a` with value `c`. -/
def delta (a : ℕ) (c : ℝ) : ℕ → ℝ := fun n => if n = a then c else 0

lemma delta_eq (a : ℕ) (c : ℝ) : delta a c a = c := by
  simp [delta]

lemma delta_ne (a : ℕ) (c : ℝ) {n : ℕ} (h : n ≠ a) : delta a c n = 0 := by
  simp [delta, h]

lemma norm_delta_le (a : ℕ) (c : ℝ) (n : ℕ) : ‖delta a c n‖ ≤ ‖c‖ := by
  classical
  by_cases h : n = a
  · subst h; simp [delta]
  · simp [delta, h]

/-- `delta a c` is integrable w.r.t. the counting measure (it has finite support). -/
lemma integrable_delta (a : ℕ) (c : ℝ) : Integrable (delta a c) Measure.count := by
  classical
  -- First show integrability on the singleton `{a}` by boundedness on a finite-measure set.
  have hs : (Measure.count ({a} : Set ℕ)) < ∞ := by simp
  have hmeas : Measurable (delta a c) := by
    -- `delta` is a measurable `ite` on a measurable singleton.
    refine measurable_ite ?_ measurable_const measurable_const
    simpa [Set.setOf_eq_eq_singleton] using (measurableSet_singleton a)
  have hASM :
      AEStronglyMeasurable (delta a c) (Measure.count.restrict ({a} : Set ℕ)) :=
    hmeas.aestronglyMeasurable
  have hbound :
      (∀ᵐ n ∂(Measure.count.restrict ({a} : Set ℕ)), ‖delta a c n‖ ≤ ‖c‖) := by
    refine Filter.eventually_of_forall ?_
    intro n
    exact norm_delta_le a c n
  have hOn : IntegrableOn (delta a c) ({a} : Set ℕ) Measure.count :=
    IntegrableOn.of_bound (μ := Measure.count) (s := ({a} : Set ℕ))
      (f := delta a c) hs hASM (C := ‖c‖) hbound
  -- Extend from `{a}` to all of `ℕ` using that `delta a c` vanishes outside `{a}`.
  refine hOn.integrable_of_forall_notMem_eq_zero ?_
  intro n hn
  have h : n ≠ a := by
    simpa [Set.mem_singleton_iff] using hn
  simp [delta, h]

/-- The integral of `delta a c` w.r.t. the counting measure is `c`. -/
lemma integral_delta (a : ℕ) (c : ℝ) : (∫ n, delta a c n ∂Measure.count) = c := by
  classical
  have hInt : Integrable (delta a c) Measure.count := integrable_delta a c
  -- Use the `countable` formula for integrals on countable types.
  simpa [delta] using
    (MeasureTheory.integral_countable' (μ := Measure.count) (f := delta a c) hInt)

/-- A spike taking value `1` at `n` and `0` elsewhere. -/
def spike (n : ℕ) : ℕ → ℝ := delta n 1

lemma integrable_spike (n : ℕ) : Integrable (spike n) Measure.count := by
  simpa [spike] using integrable_delta n 1

lemma integral_spike (n : ℕ) : (∫ k, spike n k ∂Measure.count) = 1 := by
  simpa [spike] using integral_delta n 1

/-- Pointwise: `spike n k → 0` as `n → ∞` for each fixed `k`. -/
lemma tendsto_spike_pointwise (k : ℕ) :
    Tendsto (fun n : ℕ => spike n k) atTop (𝓝 (0 : ℝ)) := by
  classical
  -- eventually, `n ≠ k`, so the function is eventually constant `0`.
  have h :
      (fun n : ℕ => spike n k) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    refine (Filter.eventually_atTop.2 ?_)
    refine ⟨k + 1, ?_⟩
    intro n hn
    have hk : n ≠ k := by
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hn
      exact ne_of_gt hklt
    simp [spike, delta, hk]
  exact (tendsto_const_nhds.congr' h)

/-- Even though `spike n → 0` pointwise, the integrals stay equal to `1`. -/
theorem spike_counterexample_limit_integral :
    (∀ k, Tendsto (fun n : ℕ => spike n k) atTop (𝓝 (0 : ℝ))) ∧
    (∀ n, (∫ k, spike n k ∂Measure.count) = 1) ∧
    ¬ Tendsto (fun n : ℕ => ∫ k, spike n k ∂Measure.count) atTop (𝓝 (0 : ℝ)) := by
  constructor
  · intro k; simpa using tendsto_spike_pointwise k
  constructor
  · intro n; simpa using integral_spike n
  · -- The integral sequence is constant `1`, so it cannot converge to `0`.
    have hconst :
        (fun n : ℕ => ∫ k, spike n k ∂Measure.count) = (fun _ : ℕ => (1 : ℝ)) := by
      funext n; simpa using integral_spike n
    intro h
    have h' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa [hconst] using h
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have : (0 : ℝ) = 1 := tendsto_nhds_unique h' h1
    exact zero_ne_one this

/-!
## A discrete Fubini counterexample

We define `F : ℕ → ℕ → ℝ` by
`F m n = 1` if `n = m`, `F m n = -1` if `n = m+1`, and `F m n = 0` otherwise.

Then:
* for each fixed `m`, `∫ n, F m n = 0`, hence `∫ m, ∫ n, F m n = 0`;
* for each fixed `n`, `∫ m, F m n = 1` if `n=0` and `0` otherwise, hence `∫ n, ∫ m, F m n = 1`.

This shows that without absolute integrability (or nonnegativity), one cannot freely swap integration order.
-/

/-- A sign-changing "two-spike" function on `ℕ × ℕ`. -/
def F (m n : ℕ) : ℝ :=
  if n = m then 1 else if n = m + 1 then (-1) else 0

lemma F_eq_delta_add (m n : ℕ) :
    F m n = delta m 1 n + delta (m + 1) (-1) n := by
  classical
  by_cases h : n = m
  · subst h; simp [F, delta]
  · by_cases h' : n = m + 1
    · subst h'; simp [F, delta, h]
    · simp [F, delta, h, h']

/-- For each fixed `m`, the `n`-integral of `F m n` is `0`. -/
lemma integral_F_right (m : ℕ) : (∫ n, F m n ∂Measure.count) = 0 := by
  classical
  -- rewrite as a sum of two deltas
  have h₁ : Integrable (delta m 1) Measure.count := integrable_delta m 1
  have h₂ : Integrable (delta (m + 1) (-1)) Measure.count := integrable_delta (m + 1) (-1)
  have hae :
      (fun n : ℕ => F m n) =ᵐ[Measure.count] (fun n => delta m 1 n + delta (m + 1) (-1) n) := by
    refine Filter.eventually_of_forall ?_
    intro n; simpa [F_eq_delta_add] using (F_eq_delta_add m n)
  calc
    ∫ n, F m n ∂Measure.count
        = ∫ n, (delta m 1 n + delta (m + 1) (-1) n) ∂Measure.count :=
          integral_congr_ae hae
    _ = (∫ n, delta m 1 n ∂Measure.count) + (∫ n, delta (m + 1) (-1) n ∂Measure.count) := by
          simpa using (integral_add (μ := Measure.count) h₁ h₂)
    _ = 1 + (-1) := by simp [integral_delta]
    _ = 0 := by simp

/-- For each fixed `n`, the `m`-integral of `F m n` is `1` for `n=0`, otherwise `0`. -/
lemma integral_F_left (n : ℕ) :
    (∫ m, F m n ∂Measure.count) = (if n = 0 then (1 : ℝ) else 0) := by
  classical
  cases n with
  | zero =>
      -- n = 0: the "-1" branch is impossible
      have hae :
          (fun m : ℕ => F m 0) =ᵐ[Measure.count] (fun m => delta 0 1 m) := by
        refine Filter.eventually_of_forall ?_
        intro m
        have : ¬ (0 = m + 1) := by
          -- `m+1 ≠ 0` in `ℕ`
          exact Nat.succ_ne_zero m |> (by simpa [Nat.succ_eq_add_one] using ·)
        by_cases h : (0 = m)
        · subst h; simp [F, delta]
        · simp [F, delta, h, this]
      calc
        ∫ m, F m 0 ∂Measure.count
            = ∫ m, delta 0 1 m ∂Measure.count := integral_congr_ae hae
        _ = 1 := by simp [integral_delta]
        _ = (if (0 : ℕ) = 0 then (1 : ℝ) else 0) := by simp
  | succ n =>
      -- n = n+1: rewrite as `delta (n+1) 1 + delta n (-1)`
      have hae :
          (fun m : ℕ => F m (n + 1))
            =ᵐ[Measure.count] (fun m => delta (n + 1) 1 m + delta n (-1) m) := by
        refine Filter.eventually_of_forall ?_
        intro m
        classical
        -- Expand the definition, noting: `n+1 = m+1` ↔ `n = m`
        by_cases h : (n + 1 = m)
        · subst h; simp [F, delta]
        · by_cases h' : (n + 1 = m + 1)
          · -- then `n = m`
            have hm : n = m := Nat.succ_inj.mp (by simpa [Nat.succ_eq_add_one] using h')
            subst hm
            simp [F, delta, h]
          · simp [F, delta, h, h']
      have h₁ : Integrable (delta (n + 1) 1) Measure.count := integrable_delta (n + 1) 1
      have h₂ : Integrable (delta n (-1)) Measure.count := integrable_delta n (-1)
      calc
        ∫ m, F m (n + 1) ∂Measure.count
            = ∫ m, (delta (n + 1) 1 m + delta n (-1) m) ∂Measure.count :=
              integral_congr_ae hae
        _ = (∫ m, delta (n + 1) 1 m ∂Measure.count) + (∫ m, delta n (-1) m ∂Measure.count) := by
              simpa using (integral_add (μ := Measure.count) h₁ h₂)
        _ = 1 + (-1) := by simp [integral_delta]
        _ = 0 := by simp
        _ = (if (Nat.succ n) = 0 then (1 : ℝ) else 0) := by simp

/-- The two iterated integrals exist but depend on the order. -/
theorem fubini_counterexample_count :
    (∫ n, (∫ m, F m n ∂Measure.count) ∂Measure.count) = (1 : ℝ) ∧
    (∫ m, (∫ n, F m n ∂Measure.count) ∂Measure.count) = (0 : ℝ) := by
  classical
  constructor
  · -- First order: integrate in `m` then in `n`
    have hae :
        (fun n : ℕ => (∫ m, F m n ∂Measure.count))
          =ᵐ[Measure.count] (fun n => if n = 0 then (1 : ℝ) else 0) := by
      refine Filter.eventually_of_forall ?_
      intro n
      simpa using (integral_F_left n)
    calc
      ∫ n, (∫ m, F m n ∂Measure.count) ∂Measure.count
          = ∫ n, (if n = 0 then (1 : ℝ) else 0) ∂Measure.count :=
            integral_congr_ae hae
      _ = ∫ n, delta 0 1 n ∂Measure.count := by
            -- `if n=0 then 1 else 0` is `delta 0 1`
            refine integral_congr_ae ?_
            refine Filter.eventually_of_forall ?_
            intro n; by_cases h : n = 0 <;> simp [delta, h]
      _ = 1 := by simp [integral_delta]
  · -- Second order: integrate in `n` then in `m`; all inner integrals are `0`.
    have hae :
        (fun m : ℕ => (∫ n, F m n ∂Measure.count))
          =ᵐ[Measure.count] (fun _m => (0 : ℝ)) := by
      refine Filter.eventually_of_forall ?_
      intro m
      simpa using (integral_F_right m)
    calc
      ∫ m, (∫ n, F m n ∂Measure.count) ∂Measure.count
          = ∫ m, (0 : ℝ) ∂Measure.count :=
            integral_congr_ae hae
      _ = 0 := by simp

end LebesgueIntegralCounterexamples
