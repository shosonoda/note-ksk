/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 02: Jordan measure

This file follows the core Jordan-measure interface from
`blueprint/src/chapters/02jordan01.tex` and
`blueprint/src/chapters/02jordan02.tex`.

Deferred Chapter 02 statements whose proofs are still placeholders live in
`NoteKsk/02jordan-statements.lean`.  This module is kept placeholder-free so
Chapter 03 and later measure-theory files can import it directly.
-/

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace NoteKsk
namespace Chapter02

/-! ## Basic sets and elementary volume -/

theorem elementaryVolume_empty {d : ℕ} :
    elementaryVolume (∅ : Set (Space d)) = 0 := by
  simp [elementaryVolume]

theorem elementaryVolume_nonneg {d : ℕ} (E : Set (Space d)) :
    0 ≤ elementaryVolume E := by
  exact bot_le

theorem elementaryVolume_mono {d : ℕ} {E F : Set (Space d)}
    (hEF : E ⊆ F) :
    elementaryVolume E ≤ elementaryVolume F := by
  exact measure_mono hEF

/-! ## Jordan measurability and null sets -/

theorem jordanMeasurable_iff {d : ℕ} {A : Set (Space d)} :
    JordanMeasurable A ↔
      Bornology.IsBounded A ∧ MeasurableSet A ∧
        jordanOuterMeasure A = jordanInnerMeasure A := by
  rfl

theorem jordanMeasure_eq_outer {d : ℕ} (A : Set (Space d)) :
    jordanMeasure A = jordanOuterMeasure A := by
  rfl

theorem jordanMeasure_eq_zero_of_null {d : ℕ} {N : Set (Space d)}
    (hN : JordanNullSet N) :
    jordanMeasure N = 0 := by
  simpa [jordanMeasure, JordanNullSet] using hN

/-! ## Compatibility with mathlib `volume` -/

/--
On Jordan-measurable sets, Jordan measure agrees with the value of mathlib's
Lebesgue measure.  Chapter 03 uses this to compare with `λ*`.
-/
theorem jordanMeasure_eq_volume_of_jordanMeasurable {d : ℕ}
    {A : Set (Space d)} (hA : JordanMeasurable A) :
    jordanMeasure A = (volume : Measure (Space d)) A := by
  have h_inner_le_volume :
      jordanInnerMeasure A ≤ (volume : Measure (Space d)) A := by
    refine iSup_le ?_
    intro E
    refine iSup_le ?_
    intro _hE
    refine iSup_le ?_
    intro hEA
    simpa [elementaryVolume] using
      (measure_mono (μ := (volume : Measure (Space d))) hEA)
  have h_volume_le_outer :
      (volume : Measure (Space d)) A ≤ jordanOuterMeasure A := by
    refine le_iInf ?_
    intro E
    refine le_iInf ?_
    intro _hE
    refine le_iInf ?_
    intro hAE
    simpa [elementaryVolume] using
      (measure_mono (μ := (volume : Measure (Space d))) hAE)
  have h_outer_le_volume :
      jordanOuterMeasure A ≤ (volume : Measure (Space d)) A := by
    simpa [hA.2.2] using h_inner_le_volume
  exact le_antisymm
    (by simpa [jordanMeasure] using h_outer_le_volume)
    (by simpa [jordanMeasure] using h_volume_le_outer)

/--
For pairwise disjoint Jordan-measurable sets, the outer value of `volume` is
countably additive.  This is stated here as the bridge needed in Chapter 03.
-/
theorem volume_iUnion_eq_tsum_of_jordanMeasurable {d : ℕ}
    (A : ℕ → Set (Space d))
    (hdisj : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (A m) (A n))
    (hA : ∀ n, JordanMeasurable (A n)) :
    (volume : Measure (Space d)) (⋃ n, A n) =
      ∑' n, (volume : Measure (Space d)) (A n) := by
  have hpair : Pairwise (Function.onFun Disjoint A) := by
    intro m n hmn
    exact hdisj hmn
  have hmeas : ∀ n, MeasurableSet (A n) := fun n => (hA n).2.1
  simpa using
    (measure_iUnion (μ := (volume : Measure (Space d))) hpair hmeas)

end Chapter02
end NoteKsk
