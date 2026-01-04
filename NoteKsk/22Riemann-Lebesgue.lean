/-
Lebesgue integration lecture notes (Lean4 + Mathlib)

This file re-formalizes (by *referencing* Mathlib):
* Representation of simple functions as a finite sum of indicators of fibers
* Simple function approximation `SimpleFunc.eapprox`
* Monotone convergence theorem for `lintegral` (Beppo Levi)

You can paste this as a standalone `.lean` file.
-/

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open scoped BigOperators ENNReal

namespace LebesgueIntegrationNotes

open MeasureTheory Set

/-!
## 1. 単関数の表現

単関数 `f : α →ₛ β` は有限値しか取らないので、値域 `f.range : Finset β` を使って
「ファイバー（逆像）の indicator の有限和」として表せる。
-/

section SimpleFuncRepresentation

variable {α β : Type*} [MeasurableSpace α]

/-- **(単関数の表現)**

`f : α →ₛ β` を、値域 `f.range` 上のファイバー indicator の有限和として表現する：

`f = ∑ y ∈ range(f), 1_{f = y} · y`

ここでは `indicator (f ⁻¹' {y}) (fun _ => y)` を使って `1_{f=y}·y` を表している。
-/
theorem SimpleFunc.coe_eq_sum_range_indicator
    [Zero β] [AddCommMonoid β] (f : MeasureTheory.SimpleFunc α β) :
    (f : α → β) =
        ∑ y in f.range, (f ⁻¹' {y}).indicator (fun _ : α => y) := by
  classical
  funext x
  -- 目標は `f x = ...` だが、有限和の評価は `sum = f x` の形が扱いやすいので `symm` する。
  have hx : f x ∈ f.range := f.mem_range_self x
  symm
  -- `simp` で indicator を ite に展開し、`Finset.sum_ite_eq_of_mem` で有限和を評価する。
  --   indicator: (s.indicator (fun _ => y)) x = if x ∈ s then y else 0
  --   x ∈ f ⁻¹' {y}  ⇔  f x = y
  simpa [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, hx] using
    (Finset.sum_ite_eq_of_mem (s := f.range) (a := f x) (b := fun y => y) hx)

end SimpleFuncRepresentation


/-!
## 2. 単関数近似 `SimpleFunc.eapprox`

`f : α → ℝ≥0∞` が可測なら、`SimpleFunc.eapprox f : ℕ → α →ₛ ℝ≥0∞` は

* `n` について単調増加
* 点ごとに `⨆ n, (eapprox f n) x = f x`
* したがって「下からの単調近似」になっている

という形で Tao の流れ（単関数→非負可測関数）と合流する。
-/

section Eapprox

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {f : α → ENNReal}

/-- `eapprox f` は `n` について単調増加（単関数列としての単調性）。 -/
theorem monotone_eapprox (f : α → ENNReal) :
    Monotone (MeasureTheory.SimpleFunc.eapprox f) :=
  MeasureTheory.SimpleFunc.monotone_eapprox f

/-- 点wise に `⨆ n, (eapprox f n) x = f x`（可測 `f` のとき）。 -/
theorem iSup_eapprox_apply (hf : Measurable f) (x : α) :
    (⨆ n : ℕ, (MeasureTheory.SimpleFunc.eapprox f n) x) = f x := by
  simpa using MeasureTheory.SimpleFunc.iSup_eapprox_apply (f := f) hf x

/-- 関数としての形：`⨆ n, (eapprox f n : α → ℝ≥0∞) = f`（可測 `f` のとき）。 -/
theorem iSup_coe_eapprox (hf : Measurable f) :
    (⨆ n : ℕ, (MeasureTheory.SimpleFunc.eapprox f n : α → ENNReal)) = f := by
  simpa using MeasureTheory.SimpleFunc.iSup_coe_eapprox (f := f) hf

/-- **(存在形の単関数近似定理)**

可測 `f : α → ℝ≥0∞` に対し、単関数列 `φ n` が

* `φ` は単調増加
* `φ n ≤ f`（点wise）
* `⨆ n, φ n = f`（点wise）

を満たす。
ここでは `φ := eapprox f` を取るだけでよい。
-/
theorem exists_monotone_simpleFunc_approx (hf : Measurable f) :
    ∃ φ : ℕ → MeasureTheory.SimpleFunc α ENNReal,
      Monotone φ ∧ (∀ n x, φ n x ≤ f x) ∧ (∀ x, (⨆ n : ℕ, φ n x) = f x) := by
  refine ⟨MeasureTheory.SimpleFunc.eapprox f, MeasureTheory.SimpleFunc.monotone_eapprox f, ?_, ?_⟩
  · intro n x
    -- φ n x ≤ ⨆ k, φ k x = f x
    have : (MeasureTheory.SimpleFunc.eapprox f n x) ≤
        (⨆ k : ℕ, MeasureTheory.SimpleFunc.eapprox f k x) :=
      le_iSup (fun k : ℕ => MeasureTheory.SimpleFunc.eapprox f k x) n
    simpa [MeasureTheory.SimpleFunc.iSup_eapprox_apply (f := f) hf x] using this
  · intro x
    simpa using MeasureTheory.SimpleFunc.iSup_eapprox_apply (f := f) hf x

/-- （講義ノート用）`lintegral` を `eapprox` の単関数積分の上限として表す。 -/
theorem lintegral_eq_iSup_eapprox_lintegral (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ⨆ n : ℕ, (MeasureTheory.SimpleFunc.eapprox f n).lintegral μ := by
  simpa using MeasureTheory.lintegral_eq_iSup_eapprox_lintegral (μ := μ) (f := f) hf

end Eapprox


/-!
## 3. 単調収束定理（Beppo Levi / MCT）

非負関数 `f n : α → ℝ≥0∞` が（点wise に）単調増加なら

`∫⁻ (⨆ n, f n) = ⨆ n, ∫⁻ f n`

が成り立つ。
-/

section MonotoneConvergence

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **単調収束定理（可測版）** -/
theorem lintegral_iSup_of_measurable
    {f : ℕ → α → ENNReal}
    (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f) :
    (∫⁻ x, (⨆ n : ℕ, f n x) ∂μ) = ⨆ n : ℕ, (∫⁻ x, f n x ∂μ) := by
  simpa using MeasureTheory.lintegral_iSup (μ := μ) (f := f) hf hmono

/-- **単調収束定理（a.e. 可測版）**

`AEMeasurable` と「a.e. 点wise 単調増加」から同じ結論。
-/
theorem lintegral_iSup_of_aeMeasurable
    {f : ℕ → α → ENNReal}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n : ℕ => f n x) :
    (∫⁻ x, (⨆ n : ℕ, f n x) ∂μ) = ⨆ n : ℕ, (∫⁻ x, f n x ∂μ) := by
  simpa using MeasureTheory.lintegral_iSup' (μ := μ) (f := f) hf hmono

end MonotoneConvergence

end LebesgueIntegrationNotes
