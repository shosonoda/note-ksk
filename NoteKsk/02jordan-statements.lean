/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«02jordan»

/-!
# Chapter 02 deferred statements

This file contains Chapter 02 statements whose proofs are not yet part of the
core dependency chain.  Chapter 03 imports `NoteKsk/02jordan.lean`, not this
module, so it does not inherit these placeholders.
-/

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace NoteKsk
namespace Chapter02

/-! ## Basic sets and elementary volume -/

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

end Chapter02
end NoteKsk
