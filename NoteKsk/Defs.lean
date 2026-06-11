/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import Mathlib

/-!
# Common definitions for the lecture notes

This file contains shared definitions used by the early chapters:

* the Lean model `Space d` of `ℝ^d`;
* axis-parallel boxes and their volumes;
* elementary sets, Jordan outer/inner measure, and Jordan measurability;
* lightweight predicates for finite additive families.
-/

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace NoteKsk

/-! ## Extended values and Euclidean spaces -/

/-- Extended real line, used in the informal exposition. -/
abbrev ExtendedReal : Type := EReal

/-- Nonnegative extended real numbers `[0, ∞]`, mathlib's value type for measures. -/
abbrev NNExtendedReal : Type := ENNReal

/-- The Lean model of `ℝ^d`. -/
abbrev Space (d : ℕ) : Type := Fin d → ℝ

/-! ## Boxes and elementary sets -/

/-- A coordinate rectangle is recorded by lower and upper endpoints. -/
structure Box (d : ℕ) where
  lower : Space d
  upper : Space d

namespace Box

variable {d : ℕ}

/-- Open rectangle `∏ i (a_i, b_i)`. -/
def Ioo (Q : Box d) : Set (Space d) :=
  Set.pi Set.univ fun i => Set.Ioo (Q.lower i) (Q.upper i)

/-- Left-open/right-closed rectangle `∏ i (a_i, b_i]`. -/
def Ioc (Q : Box d) : Set (Space d) :=
  Set.pi Set.univ fun i => Set.Ioc (Q.lower i) (Q.upper i)

/-- Left-closed/right-open rectangle `∏ i [a_i, b_i)`. -/
def Ico (Q : Box d) : Set (Space d) :=
  Set.pi Set.univ fun i => Set.Ico (Q.lower i) (Q.upper i)

/-- Closed rectangle `∏ i [a_i, b_i]`. -/
def Icc (Q : Box d) : Set (Space d) :=
  Set.Icc Q.lower Q.upper

/-- The formal volume of a rectangle, `∏ i (b_i - a_i)`, as an `ENNReal`. -/
def volume (Q : Box d) : ENNReal :=
  ∏ i, ENNReal.ofReal (Q.upper i - Q.lower i)

/-- A nondegenerate finite rectangle. -/
def Nondegenerate (Q : Box d) : Prop :=
  ∀ i, Q.lower i < Q.upper i

end Box

/-! ## Standard windows -/

/-- The closed cube `[-R, R]^d`, bundled as a `Box`. -/
def closedCubeBox (d : ℕ) (R : ℝ) : Box d where
  lower := fun _ => -R
  upper := fun _ => R

/-- The closed cube `Q_R = [-R, R]^d` used to localize unbounded sets. -/
def closedCube (d : ℕ) (R : ℝ) : Set (Space d) :=
  (closedCubeBox d R).Icc

/--
The family `𝓔_d`: left half-open rectangles together with the empty set.
Endpoints are finite real numbers at this stage of the development.
-/
def IsLeftHalfOpenBox {d : ℕ} (S : Set (Space d)) : Prop :=
  S = ∅ ∨ ∃ Q : Box d, Q.Nondegenerate ∧ Q.Ioc = S

/--
Elementary sets `𝓐_d`: finite disjoint unions of nondegenerate left half-open boxes.
-/
def IsElementarySet {d : ℕ} (S : Set (Space d)) : Prop :=
  ∃ n : ℕ, ∃ Q : Fin n → Box d,
    (∀ j, (Q j).Nondegenerate) ∧
    (∀ ⦃i j : Fin n⦄, i ≠ j → Disjoint ((Q i).Ioc) ((Q j).Ioc)) ∧
    S = ⋃ j, (Q j).Ioc

/--
The volume assigned to an elementary set.  This is deliberately defined by
mathlib's `volume` for now; Chapter 2 later proves that this agrees with the
finite disjoint-box presentation.
-/
def elementaryVolume {d : ℕ} (E : Set (Space d)) : ENNReal :=
  (volume : Measure (Space d)) E

/-- Translate a set by a vector. -/
def translate {d : ℕ} (A : Set (Space d)) (c : Space d) : Set (Space d) :=
  (fun x => x + c) '' A

/-! ## Jordan outer and inner content -/

/-- Jordan outer measure: infimum of elementary volumes over elementary supersets. -/
def jordanOuterMeasure {d : ℕ} (A : Set (Space d)) : ENNReal :=
  ⨅ E : Set (Space d), ⨅ _hE : IsElementarySet E, ⨅ _hAE : A ⊆ E, elementaryVolume E

/-- Jordan inner measure: supremum of elementary volumes over elementary subsets. -/
def jordanInnerMeasure {d : ℕ} (A : Set (Space d)) : ENNReal :=
  ⨆ E : Set (Space d), ⨆ _hE : IsElementarySet E, ⨆ _hEA : E ⊆ A, elementaryVolume E

/--
Jordan measurability, restricted to bounded sets as in the notes.

The `MeasurableSet` field records the later theorem that Jordan-measurable sets
are Lebesgue measurable; this lets Chapter 03 use mathlib's countable additivity
of `volume` without adding another placeholder.
-/
def JordanMeasurable {d : ℕ} (A : Set (Space d)) : Prop :=
  Bornology.IsBounded A ∧ MeasurableSet A ∧ jordanOuterMeasure A = jordanInnerMeasure A

/-- Jordan measure of a Jordan-measurable set, represented by the outer value. -/
def jordanMeasure {d : ℕ} (A : Set (Space d)) : ENNReal :=
  jordanOuterMeasure A

/-- Jordan null sets. -/
def JordanNullSet {d : ℕ} (A : Set (Space d)) : Prop :=
  jordanOuterMeasure A = 0

/-! ## Finite additive families -/

/-- A finite additive family of subsets. -/
def FiniteAdditiveFamily {α : Type*} (𝓕 : Set (Set α)) : Prop :=
  (∅ : Set α) ∈ 𝓕 ∧
    (∀ A, A ∈ 𝓕 → Aᶜ ∈ 𝓕) ∧
    (∀ A B, A ∈ 𝓕 → B ∈ 𝓕 → A ∪ B ∈ 𝓕)

end NoteKsk
