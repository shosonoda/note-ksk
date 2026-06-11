/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«01riemann»

/-!
# Chapter 02: Jordan measure

This file follows `blueprint/src/chapters/02jordan01.tex` and
`blueprint/src/chapters/02jordan02.tex`.

It introduces the Jordan-measure interface used by Chapter 03.  Many proofs are
left as `sorry` while the global dependency graph is stabilized.
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

/-- Grid subdivision: finite unions of left half-open boxes are elementary sets. -/
theorem elementarySet_finite_union_leftHalfOpenBoxes {d n : ℕ}
    (Q : Fin n → Box d) (hQ : ∀ j, (Q j).Nondegenerate) :
    IsElementarySet (⋃ j, (Q j).Ioc) := by
  sorry

/-- Elementary volume is independent of the chosen disjoint presentation. -/
theorem elementaryVolume_eq_sum_boxVolume {d n : ℕ}
    (Q : Fin n → Box d)
    (hQ : ∀ j, (Q j).Nondegenerate)
    (hdisj : ∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint ((Q i).Ioc) ((Q j).Ioc)) :
    elementaryVolume (⋃ j, (Q j).Ioc) = ∑ j, (Q j).volume := by
  sorry

theorem elementaryVolume_union_of_disjoint {d : ℕ} {E F : Set (Space d)}
    (hE : IsElementarySet E) (hF : IsElementarySet F) (hdisj : Disjoint E F) :
    elementaryVolume (E ∪ F) = elementaryVolume E + elementaryVolume F := by
  sorry

theorem elementaryVolume_translate {d : ℕ}
    {E : Set (Space d)} (hE : IsElementarySet E) (c : Space d) :
    elementaryVolume (translate E c) = elementaryVolume E := by
  sorry

/-! ## Jordan outer and inner measure -/

theorem jordanInnerMeasure_le_jordanOuterMeasure {d : ℕ} (A : Set (Space d)) :
    jordanInnerMeasure A ≤ jordanOuterMeasure A := by
  sorry

theorem jordanOuterMeasure_mono {d : ℕ} {A B : Set (Space d)} (hAB : A ⊆ B) :
    jordanOuterMeasure A ≤ jordanOuterMeasure B := by
  sorry

theorem jordanInnerMeasure_mono {d : ℕ} {A B : Set (Space d)} (hAB : A ⊆ B) :
    jordanInnerMeasure A ≤ jordanInnerMeasure B := by
  sorry

theorem jordanOuterMeasure_empty {d : ℕ} :
    jordanOuterMeasure (∅ : Set (Space d)) = 0 := by
  sorry

theorem jordanInnerMeasure_empty {d : ℕ} :
    jordanInnerMeasure (∅ : Set (Space d)) = 0 := by
  sorry

theorem jordanOuterMeasure_finite_subadditive {d n : ℕ}
    (A : Fin n → Set (Space d)) :
    jordanOuterMeasure (⋃ i, A i) ≤ ∑ i, jordanOuterMeasure (A i) := by
  sorry

/-! ## Jordan measurability and null sets -/

theorem jordanMeasurable_iff {d : ℕ} {A : Set (Space d)} :
    JordanMeasurable A ↔
      Bornology.IsBounded A ∧ MeasurableSet A ∧
        jordanOuterMeasure A = jordanInnerMeasure A := by
  rfl

theorem jordanMeasure_eq_outer {d : ℕ} (A : Set (Space d)) :
    jordanMeasure A = jordanOuterMeasure A := by
  rfl

theorem elementarySet_jordanMeasurable {d : ℕ} {E : Set (Space d)}
    (hE : IsElementarySet E) (hEbdd : Bornology.IsBounded E) :
    JordanMeasurable E := by
  sorry

theorem jordanMeasure_elementarySet {d : ℕ} {E : Set (Space d)}
    (hE : IsElementarySet E) (hEbdd : Bornology.IsBounded E) :
    jordanMeasure E = elementaryVolume E := by
  sorry

theorem jordanNullSet_jordanMeasurable {d : ℕ} {N : Set (Space d)}
    (hN : JordanNullSet N) (hNbdd : Bornology.IsBounded N) :
    JordanMeasurable N := by
  sorry

theorem jordanMeasure_eq_zero_of_null {d : ℕ} {N : Set (Space d)}
    (hN : JordanNullSet N) :
    jordanMeasure N = 0 := by
  simpa [jordanMeasure, JordanNullSet] using hN

theorem jordanNullSet_singleton {d : ℕ} (x : Space d) :
    JordanNullSet ({x} : Set (Space d)) := by
  sorry

theorem jordanNullSet_finite {d : ℕ} {N : Set (Space d)}
    (hN : N.Finite) :
    JordanNullSet N := by
  sorry

theorem jordanNullSet_boundary_elementary {d : ℕ} {E : Set (Space d)}
    (hE : IsElementarySet E) :
    JordanNullSet (frontier E) := by
  sorry

/-! ## Jordan measurability criteria -/

theorem jordanMeasurable_iff_boundary_null {d : ℕ} {A : Set (Space d)}
    (hAbdd : Bornology.IsBounded A) :
    JordanMeasurable A ↔ JordanNullSet (frontier A) := by
  sorry

theorem jordanMeasurable_iff_indicator_riemannIntegrable {d : ℕ}
    {A I : Set (Space d)}
    (hAbdd : Bornology.IsBounded A) (hAI : A ⊆ I) :
    JordanMeasurable A ↔ True := by
  -- TODO: replace `True` by the multidimensional Riemann integrability
  -- of the indicator function on the box `I`.
  sorry

theorem riemannIntegral_indicator_eq_jordanMeasure {d : ℕ}
    {A I : Set (Space d)} (_hA : JordanMeasurable A) (_hAI : A ⊆ I) :
    True := by
  -- TODO: state this using the multidimensional Riemann integral of `1_A`.
  trivial

/-! ## Finite additivity and finite additive families -/

theorem jordanMeasurable_union {d : ℕ} {A B : Set (Space d)}
    (hA : JordanMeasurable A) (hB : JordanMeasurable B) :
    JordanMeasurable (A ∪ B) := by
  sorry

theorem jordanMeasurable_inter {d : ℕ} {A B : Set (Space d)}
    (hA : JordanMeasurable A) (hB : JordanMeasurable B) :
    JordanMeasurable (A ∩ B) := by
  sorry

theorem jordanMeasurable_compl_in_box {d : ℕ} {A I : Set (Space d)}
    (hA : JordanMeasurable A) (hI : IsElementarySet I) :
    JordanMeasurable (I \ A) := by
  sorry

theorem jordanMeasure_union {d : ℕ} {A B : Set (Space d)}
    (hA : JordanMeasurable A) (hB : JordanMeasurable B) :
    jordanMeasure (A ∪ B) =
      jordanMeasure A + jordanMeasure B - jordanMeasure (A ∩ B) := by
  sorry

theorem jordanMeasure_union_of_disjoint {d : ℕ} {A B : Set (Space d)}
    (hA : JordanMeasurable A) (hB : JordanMeasurable B)
    (hdisj : Disjoint A B) :
    jordanMeasure (A ∪ B) = jordanMeasure A + jordanMeasure B := by
  sorry

theorem jordanMeasurable_iUnion_fin {d n : ℕ}
    (A : Fin n → Set (Space d)) (hA : ∀ i, JordanMeasurable (A i)) :
    JordanMeasurable (⋃ i, A i) := by
  sorry

theorem jordanMeasurableSets_finiteAdditiveFamily {d : ℕ} :
    FiniteAdditiveFamily { A : Set (Space d) | JordanMeasurable A } := by
  sorry

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
