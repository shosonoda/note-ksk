/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«05lebesgue-measure»

/-!
# Chapter 06: Carathéodory-style measure theory

This file follows the active blueprint file
`blueprint/src/chapters/06caratheodory02.tex`.

The chapter is aligned with mathlib's measure-theory API:

* σ-algebras are `MeasurableSpace`s;
* outer measures are `OuterMeasure`s;
* Carathéodory-measurable sets are `OuterMeasure.IsCaratheodory`;
* semirings of sets are `IsSetSemiring`;
* premeasures on semirings are represented by `AddContent ENNReal C` together
  with `AddContent.IsSigmaSubadditive`;
* the Carathéodory--Hahn extension is mathlib's `AddContent.measure` and
  `AddContent.measureCaratheodory`.

Differences from the lecture text are noted near the relevant statements.
Chapter 6.7 is an expository survey in the notes, so it is not formalized here.
-/

noncomputable section

open scoped BigOperators Topology ENNReal Function
open Set MeasureTheory

namespace NoteKsk
open Chapter03 Chapter05

namespace Chapter06

/-! ## 2. Measurable spaces and measures -/

section SigmaAlgebra

variable {α : Type*}

/-- Members of the generated σ-algebra contain the original generating family. -/
theorem generatedSigmaAlgebra_contains {C : Set (Set α)} {s : Set α}
    (hs : s ∈ C) :
    MeasurableSet[generatedSigmaAlgebra C] s := by
  exact MeasurableSpace.measurableSet_generateFrom hs

/-- The generated σ-algebra is the smallest σ-algebra containing the given family. -/
theorem generatedSigmaAlgebra_minimal {C : Set (Set α)} {m : MeasurableSpace α}
    (hC : ∀ s ∈ C, MeasurableSet[m] s) :
    generatedSigmaAlgebra C ≤ m := by
  exact MeasurableSpace.generateFrom_le hC

variable [MeasurableSpace α]

theorem sigmaAlgebra_empty_mem :
    MeasurableSet (∅ : Set α) := by
  exact MeasurableSet.empty

theorem sigmaAlgebra_univ_mem :
    MeasurableSet (Set.univ : Set α) := by
  exact MeasurableSet.univ

theorem sigmaAlgebra_compl_mem {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet Aᶜ := by
  exact hA.compl

theorem sigmaAlgebra_iUnion_mem (A : ℕ → Set α)
    (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (⋃ n, A n) := by
  exact MeasurableSet.iUnion hA

theorem measure_empty (μ : Measure α) :
    μ (∅ : Set α) = 0 := by
  simp

theorem measure_iUnion_disjoint (μ : Measure α) (A : ℕ → Set α)
    (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Disjoint on A)) :
    μ (⋃ n, A n) = ∑' n, μ (A n) := by
  exact measure_iUnion hdisj hA

/-- σ-finiteness, stated as the usual measurable countable exhaustion. -/
theorem sigmaFinite_iff_exists_measurable_finite_spanning (μ : Measure α) :
    SigmaFinite μ ↔
      ∃ S : ℕ → Set α,
        (∀ n, MeasurableSet (S n)) ∧
        (∀ n, μ (S n) < ∞) ∧
        (⋃ n, S n) = Set.univ := by
  constructor
  · intro hμ
    letI : SigmaFinite μ := hμ
    refine ⟨μ.toFiniteSpanningSetsIn.set, ?_, ?_, ?_⟩
    · exact μ.toFiniteSpanningSetsIn.set_mem
    · exact μ.toFiniteSpanningSetsIn.finite
    · exact μ.toFiniteSpanningSetsIn.spanning
  · rintro ⟨S, hSmeas, hSfin, hSspan⟩
    let hspan : μ.FiniteSpanningSetsIn {T : Set α | MeasurableSet T} :=
      ⟨S, hSmeas, hSfin, hSspan⟩
    exact hspan.sigmaFinite

/-- Counting measure assigns the cardinality to a measurable set. -/
theorem countingMeasure_apply {A : Set α} (hA : MeasurableSet A) :
    Measure.count A = A.encard := by
  exact Measure.count_apply hA

/-- Dirac measure, in the mathlib form using `indicator`. -/
theorem diracMeasure_apply [MeasurableSingletonClass α] (a : α) (A : Set α) :
    Measure.dirac a A = A.indicator (fun _ => (1 : ENNReal)) a := by
  exact Measure.dirac_apply a A

end SigmaAlgebra

/-! ## 3. Outer measures and Carathéodory measurability -/

section OuterMeasure

variable {α : Type*}

theorem outerMeasure_empty (μ : OuterMeasure α) :
    μ (∅ : Set α) = 0 := by
  simp

theorem outerMeasure_mono (μ : OuterMeasure α) {A B : Set α}
    (hAB : A ⊆ B) :
    μ A ≤ μ B := by
  exact μ.mono hAB

theorem outerMeasure_iUnion_le (μ : OuterMeasure α) (A : ℕ → Set α) :
    μ (⋃ n, A n) ≤ ∑' n, μ (A n) := by
  exact measure_iUnion_le (μ := μ) A

theorem caratheodoryMeasurable_iff {μ : OuterMeasure α} {A : Set α} :
    CaratheodoryMeasurableSet μ A ↔
      ∀ E, μ E = μ (E ∩ A) + μ (E \ A) := by
  rfl

theorem caratheodory_empty (μ : OuterMeasure α) :
    CaratheodoryMeasurableSet μ (∅ : Set α) := by
  exact OuterMeasure.isCaratheodory_empty μ

theorem caratheodory_univ (μ : OuterMeasure α) :
    CaratheodoryMeasurableSet μ (Set.univ : Set α) := by
  simpa using
    (OuterMeasure.isCaratheodory_compl μ (OuterMeasure.isCaratheodory_empty μ))

theorem caratheodory_compl {μ : OuterMeasure α} {A : Set α}
    (hA : CaratheodoryMeasurableSet μ A) :
    CaratheodoryMeasurableSet μ Aᶜ := by
  exact OuterMeasure.isCaratheodory_compl μ hA

theorem caratheodory_union {μ : OuterMeasure α} {A B : Set α}
    (hA : CaratheodoryMeasurableSet μ A)
    (hB : CaratheodoryMeasurableSet μ B) :
    CaratheodoryMeasurableSet μ (A ∪ B) := by
  exact OuterMeasure.isCaratheodory_union μ hA hB

theorem caratheodory_inter {μ : OuterMeasure α} {A B : Set α}
    (hA : CaratheodoryMeasurableSet μ A)
    (hB : CaratheodoryMeasurableSet μ B) :
    CaratheodoryMeasurableSet μ (A ∩ B) := by
  exact OuterMeasure.isCaratheodory_inter μ hA hB

theorem caratheodory_iUnion {μ : OuterMeasure α} (A : ℕ → Set α)
    (hA : ∀ n, CaratheodoryMeasurableSet μ (A n)) :
    CaratheodoryMeasurableSet μ (⋃ n, A n) := by
  exact OuterMeasure.isCaratheodory_iUnion μ hA

/-- The σ-algebra of Carathéodory-measurable sets. -/
theorem caratheodoryMeasurableSpace_iff {μ : OuterMeasure α} {A : Set α} :
    MeasurableSet[caratheodoryMeasurableSpace μ] A ↔
      CaratheodoryMeasurableSet μ A := by
  rfl

theorem caratheodory_outerMeasure_iUnion_eq_tsum {μ : OuterMeasure α}
    (A : ℕ → Set α)
    (hA : ∀ n, MeasurableSet[caratheodoryMeasurableSpace μ] (A n))
    (hdisj : Pairwise (Disjoint on A)) :
    μ (⋃ n, A n) = ∑' n, μ (A n) := by
  exact OuterMeasure.iUnion_eq_of_caratheodory μ hA hdisj

/-- Null subsets are measurable in the completed measurable structure. -/
theorem null_subset_completedMeasurableSet {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N A : Set α} (hN : μ N = 0) (hA : A ⊆ N) :
    CompletedMeasurableSet μ A := by
  exact NullMeasurableSet.of_null (measure_mono_null hA hN)

theorem measure_completion_isComplete {α : Type*} [MeasurableSpace α]
    (μ : Measure α) :
    μ.completion.IsComplete := by
  infer_instance

end OuterMeasure

/-! ## 4. Semirings and premeasures -/

section Semiring

variable {α : Type*} {C : Set (Set α)}

/-- The whole powerset is a semiring of sets. -/
theorem powerset_isSetSemiring :
    IsSetSemiring (Set.univ : Set (Set α)) := by
  refine ⟨by trivial, ?_, ?_⟩
  · intro s _ t _
    trivial
  · intro s _ t _
    refine ⟨{s \ t}, by intro u _; trivial, ?_, ?_⟩
    · simp
    · simp

private theorem isLeftHalfOpenBox_isCoverBoxSet {d : ℕ} {S : Set (Space d)}
    (hS : IsLeftHalfOpenBox S) :
    IsCoverBoxSet S := by
  rcases hS with rfl | ⟨Q, _hQ, hQS⟩
  · exact IsCoverBoxSet.empty
  · exact ⟨CoverBox.box Q, by simpa [CoverBox.carrier] using hQS⟩

private theorem isCoverBoxSet_isLeftHalfOpenBox {d : ℕ} {S : Set (Space d)}
    (hS : IsCoverBoxSet S) :
    IsLeftHalfOpenBox S := by
  rcases hS with ⟨R, rfl⟩
  cases R with
  | empty =>
      exact Or.inl rfl
  | box Q =>
      by_cases hQ : Q.Nondegenerate
      · exact Or.inr ⟨Q, hQ, rfl⟩
      · exact Or.inl <| by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          have hx' : ∀ i, Q.lower i < x i ∧ x i ≤ Q.upper i := by
            simpa [CoverBox.carrier, Box.Ioc, Set.mem_pi] using hx
          have hQ' : ¬ ∀ i, Q.lower i < Q.upper i := by
            simpa [Box.Nondegenerate] using hQ
          rcases not_forall.mp hQ' with ⟨i, hi⟩
          exact hi (lt_of_lt_of_le (hx' i).1 (hx' i).2)

/-- The left half-open boxes from the earlier chapters form a semiring. -/
theorem leftHalfOpenBox_isSetSemiring {d : ℕ} :
    IsSetSemiring {S : Set (Space d) | IsLeftHalfOpenBox S} := by
  let hcover : IsSetSemiring {S : Set (Space d) | IsCoverBoxSet S} :=
    IsCoverBoxSet.isSetSemiring d
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · intro S hS T hT
    exact isCoverBoxSet_isLeftHalfOpenBox
      (hcover.inter_mem S (isLeftHalfOpenBox_isCoverBoxSet hS)
        T (isLeftHalfOpenBox_isCoverBoxSet hT))
  · intro S hS T hT
    rcases hcover.diff_eq_sUnion' S (isLeftHalfOpenBox_isCoverBoxSet hS)
        T (isLeftHalfOpenBox_isCoverBoxSet hT) with ⟨I, hI, hdisj, hdiff⟩
    refine ⟨I, ?_, hdisj, hdiff⟩
    intro U hU
    exact isCoverBoxSet_isLeftHalfOpenBox (hI hU)

/-- A semiring generates a ring of sets by finite unions. -/
theorem algebraGeneratedBySemiring_isSetRing (hC : IsSetSemiring C) :
    IsSetRing (algebraGeneratedBySemiring C) := by
  exact hC.isSetRing_supClosure

/-- Finite unions of generators are measurable in the generated σ-algebra. -/
theorem algebraGeneratedBySemiring_measurable {s : Set α}
    (hs : s ∈ algebraGeneratedBySemiring C) :
    MeasurableSet[generatedSigmaAlgebra C] s := by
  exact measurableSet_generateFrom_of_mem_supClosure hs

/--
Extension of an additive content from a semiring to its finite-union algebra.

This is the theorem `thm:premeasure-extension-to-algebra` in mathlib's form:
`AddContent.supClosure`.
-/
noncomputable def premeasureExtensionToAlgebra (hC : IsSetSemiring C)
    (m : AddContent ENNReal C) :
    AddContent ENNReal (algebraGeneratedBySemiring C) :=
  m.supClosure hC

theorem premeasureExtensionToAlgebra_eq_on_semiring
    (hC : IsSetSemiring C) (m : AddContent ENNReal C)
    {s : Set α} (hs : s ∈ C) :
    premeasureExtensionToAlgebra hC m s = m s := by
  exact AddContent.supClosure_apply_of_mem hC m hs

/--
If the original content is a premeasure, then its finite-algebra extension is a
premeasure.

The proof compares `AddContent.supClosure` with the measure generated by `m`
on `generatedSigmaAlgebra C`; countable subadditivity then follows from the
outer-measure subadditivity of that generated measure.
-/
theorem premeasureExtensionToAlgebra_isPremeasure
    (hC : IsSetSemiring C) (m : AddContent ENNReal C)
    (hm : IsPremeasureOnSemiring m) :
    IsPremeasureOnSemiring (premeasureExtensionToAlgebra hC m) := by
  intro f hf hU
  letI : MeasurableSpace α := generatedSigmaAlgebra C
  let μ : Measure α := m.measure hC le_rfl hm
  have h_eq : ∀ {s : Set α}, s ∈ algebraGeneratedBySemiring C →
      μ s = premeasureExtensionToAlgebra hC m s := by
    intro s hs
    rcases hC.mem_supClosure_iff.mp hs with ⟨P, hP⟩
    have hmeas : ∀ b ∈ P.parts, MeasurableSet b := by
      intro b hb
      exact MeasurableSpace.measurableSet_generateFrom (hP hb)
    have hμpart : ∀ b ∈ P.parts, μ b = m b := by
      intro b hb
      simpa [μ, generatedSigmaAlgebra, IsPremeasureOnSemiring] using
        AddContent.measure_eq (m := m) (hC := hC)
          (hC_gen := (rfl : generatedSigmaAlgebra C = MeasurableSpace.generateFrom C))
          (m_sigma_subadd := hm) (hP hb)
    have h_union : (⋃ b ∈ P.parts, b) = s := by
      simpa [Finset.sup_set_eq_biUnion] using P.sup_parts
    calc
      μ s = μ (⋃ b ∈ P.parts, b) := by
        rw [h_union]
      _ = ∑ b ∈ P.parts, μ b := by
        simpa using
          (measure_biUnion_finset (μ := μ) (s := P.parts) (f := id) P.disjoint hmeas)
      _ = ∑ b ∈ P.parts, m b := by
        exact Finset.sum_congr rfl fun b hb => hμpart b hb
      _ = premeasureExtensionToAlgebra hC m s := by
        rw [premeasureExtensionToAlgebra]
        exact (AddContent.supClosure_apply_finpartition hC m hP).symm
  calc
    premeasureExtensionToAlgebra hC m (⋃ i, f i) = μ (⋃ i, f i) := (h_eq hU).symm
    _ ≤ ∑' i, μ (f i) := measure_iUnion_le (μ := μ) f
    _ = ∑' i, premeasureExtensionToAlgebra hC m (f i) := by
      exact tsum_congr fun i => h_eq (hf i)

end Semiring

/-! ## 5. Induced outer measures and extension theorems -/

section Extension

variable {α : Type*} {C : Set (Set α)}

/-- The outer measure induced by a semiring premeasure via countable covers. -/
noncomputable def inducedOuterMeasureFromPremeasure
    (hC : IsSetSemiring C) (m : AddContent ENNReal C) : OuterMeasure α :=
  inducedOuterMeasure (fun s (_hs : s ∈ C) => m s) hC.empty_mem (by simp)

theorem inducedOuterMeasureFromPremeasure_eq_on_semiring
    (hC : IsSetSemiring C) (m : AddContent ENNReal C)
    (hm : IsPremeasureOnSemiring m) {s : Set α} (hs : s ∈ C) :
    inducedOuterMeasureFromPremeasure hC m s = m s := by
  simpa [inducedOuterMeasureFromPremeasure, IsPremeasureOnSemiring] using
    AddContent.inducedOuterMeasure_eq hC m hm hs

theorem inducedOuterMeasureFromPremeasure_caratheodory_of_mem
    (hC : IsSetSemiring C) (m : AddContent ENNReal C)
    {s : Set α} (hs : s ∈ C) :
    CaratheodoryMeasurableSet (inducedOuterMeasureFromPremeasure hC m) s := by
  simpa [CaratheodoryMeasurableSet, inducedOuterMeasureFromPremeasure] using
    AddContent.isCaratheodory_inducedOuterMeasure_of_mem hC m hs

theorem inducedOuterMeasureFromPremeasure_caratheodory_generated
    (hC : IsSetSemiring C) (m : AddContent ENNReal C)
    {s : Set α} (hs : MeasurableSet[generatedSigmaAlgebra C] s) :
    CaratheodoryMeasurableSet (inducedOuterMeasureFromPremeasure hC m) s := by
  simpa [CaratheodoryMeasurableSet, inducedOuterMeasureFromPremeasure, generatedSigmaAlgebra] using
    AddContent.isCaratheodory_inducedOuterMeasure hC m s hs

/-- A measure generated from a semiring premeasure on the current measurable space. -/
noncomputable def measureFromPremeasure [MeasurableSpace α]
    (hC : IsSetSemiring C)
    (hgen : ‹MeasurableSpace α› ≤ generatedSigmaAlgebra C)
    (m : AddContent ENNReal C) (hm : IsPremeasureOnSemiring m) :
    Measure α :=
  m.measure hC hgen hm

theorem measureFromPremeasure_eq_on_semiring [MeasurableSpace α]
    (hC : IsSetSemiring C)
    (hgen : ‹MeasurableSpace α› = generatedSigmaAlgebra C)
    (m : AddContent ENNReal C) (hm : IsPremeasureOnSemiring m)
    {s : Set α} (hs : s ∈ C) :
    measureFromPremeasure hC hgen.le m hm s = m s := by
  simpa [measureFromPremeasure, generatedSigmaAlgebra, IsPremeasureOnSemiring] using
    AddContent.measure_eq (m := m) (hC := hC) (hC_gen := hgen)
      (m_sigma_subadd := hm) hs

/--
Existence part of the Carathéodory--Hahn extension theorem.

Compared with the lecture statement, the generated measurable space is made
explicit in the type of the resulting measure.
-/
theorem caratheodoryHahn_extension_exists
    (hC : IsSetSemiring C) (m : AddContent ENNReal C)
    (hm : IsPremeasureOnSemiring m) :
    ∃ μ : @Measure α (generatedSigmaAlgebra C), ∀ s, s ∈ C → μ s = m s := by
  letI : MeasurableSpace α := generatedSigmaAlgebra C
  refine ⟨m.measure hC le_rfl hm, ?_⟩
  intro s hs
  simpa [generatedSigmaAlgebra, IsPremeasureOnSemiring] using
    AddContent.measure_eq (m := m) (hC := hC)
      (hC_gen := (rfl : generatedSigmaAlgebra C = MeasurableSpace.generateFrom C))
      (m_sigma_subadd := hm) hs

/--
Uniqueness part in mathlib's standard form.

The lecture notes state uniqueness under σ-finiteness on the generating
semiring.  Mathlib uses the more concrete hypothesis
`μ.FiniteSpanningSetsIn C`: a countable cover by members of the generator, each
with finite `μ`-measure.  This implies σ-finiteness and is the version used by
`Measure.FiniteSpanningSetsIn.ext`.
-/
theorem caratheodoryHahn_extension_unique [MeasurableSpace α]
    (hgen : ‹MeasurableSpace α› = generatedSigmaAlgebra C)
    (hπ : IsPiSystem C) {μ ν : Measure α}
    (hspan : μ.FiniteSpanningSetsIn C)
    (hμν : ∀ s, s ∈ C → μ s = ν s) :
    μ = ν := by
  exact hspan.ext hgen hπ hμν

theorem caratheodoryHahn_extension_unique_of_semiring [MeasurableSpace α]
    (hgen : ‹MeasurableSpace α› = generatedSigmaAlgebra C)
    (hC : IsSetSemiring C) {μ ν : Measure α}
    (hspan : μ.FiniteSpanningSetsIn C)
    (hμν : ∀ s, s ∈ C → μ s = ν s) :
    μ = ν := by
  exact caratheodoryHahn_extension_unique hgen hC.isPiSystem hspan hμν

/--
The Lebesgue outer measure is the outer measure induced by the premeasure on
left half-open boxes.

The exact construction depends on reconciling the Chapter 03 box content with
mathlib's `AddContent` API, so this is left as a named bridge theorem.
-/
theorem lambdaStar_eq_inducedOuterMeasureFromBoxes {d : ℕ} :
    ∃ m : AddContent ENNReal {S : Set (Space d) | IsLeftHalfOpenBox S},
      IsPremeasureOnSemiring m ∧
      (∀ A : Set (Space d),
        lambdaStar A =
          inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m A) := by
  let m : AddContent ENNReal {S : Set (Space d) | IsLeftHalfOpenBox S} := {
    toFun := fun S => lambdaStar S
    empty' := by
      change lambdaStar (∅ : Set (Space d)) = 0
      simp [lambdaStar]
    sUnion' := by
      intro I hI hdis _hmem
      have hmeas : ∀ S ∈ (I : Set (Set (Space d))), MeasurableSet S := by
        intro S hS
        exact IsCoverBoxSet.measurableSet (isLeftHalfOpenBox_isCoverBoxSet (hI hS))
      change lambdaStar (⋃₀ (I : Set (Set (Space d)))) =
        ∑ S ∈ I, lambdaStar S
      rw [lambdaStar, measure_sUnion I.countable_toSet hdis hmeas]
      exact I.tsum_subtype (fun S : Set (Space d) => (volume : Measure (Space d)) S) }
  have hm : IsPremeasureOnSemiring m := by
    intro f _hf _hUnion
    simpa [m, IsPremeasureOnSemiring, lambdaStar] using
      (measure_iUnion_le (μ := (volume : Measure (Space d))) f)
  refine ⟨m, hm, ?_⟩
  intro A
  have hinduced_eq_boxes :
      inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m A =
        lambdaStarByBoxes A := by
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro Q
      refine le_iInf ?_
      intro hQ
      calc
        inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m A ≤
            inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m
              (⋃ n, (Q n).carrier) :=
          (inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m).mono hQ
        _ ≤ ∑' n,
            inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m
              ((Q n).carrier) := by
          exact measure_iUnion_le
            (μ := inducedOuterMeasureFromPremeasure leftHalfOpenBox_isSetSemiring m)
            fun n => (Q n).carrier
        _ = boxCoverCost Q := by
          unfold boxCoverCost
          apply tsum_congr
          intro n
          have hcarrier : IsLeftHalfOpenBox (Q n).carrier :=
            isCoverBoxSet_isLeftHalfOpenBox ⟨Q n, rfl⟩
          rw [inducedOuterMeasureFromPremeasure_eq_on_semiring
            leftHalfOpenBox_isSetSemiring m hm hcarrier]
          exact CoverBox.lambdaStar_carrier_eq_volume (Q n)
    · classical
      rw [inducedOuterMeasureFromPremeasure, inducedOuterMeasure]
      rw [OuterMeasure.ofFunction_eq_iInf_mem
        (P := fun S : Set (Space d) => IsLeftHalfOpenBox S)
        (m_top := by
          intro S hS
          exact extend_eq_top
            (m := fun S (_hS : IsLeftHalfOpenBox S) => m S) hS)]
      refine le_iInf ?_
      intro T
      refine le_iInf ?_
      intro hT
      refine le_iInf ?_
      intro hcov
      choose Q hQ using fun n => isLeftHalfOpenBox_isCoverBoxSet (hT n)
      have hQcover : IsBoxCover A Q := by
        intro x hx
        rcases Set.mem_iUnion.mp (hcov hx) with ⟨n, hxn⟩
        exact Set.mem_iUnion.mpr ⟨n, by simpa [hQ n] using hxn⟩
      have hle_cost : lambdaStarByBoxes A ≤ boxCoverCost Q :=
        (iInf_le
          (fun Q : ℕ → CoverBox d => ⨅ _hQ : IsBoxCover A Q, boxCoverCost Q) Q).trans
          (iInf_le (fun _hQ : IsBoxCover A Q => boxCoverCost Q) hQcover)
      refine hle_cost.trans_eq ?_
      unfold boxCoverCost
      apply tsum_congr
      intro n
      calc
        (Q n).volume = lambdaStar (T n) := by
          rw [← hQ n]
          exact (CoverBox.lambdaStar_carrier_eq_volume (Q n)).symm
        _ = m (T n) := rfl
        _ = extend (fun S (_hS : IsLeftHalfOpenBox S) => m S) (T n) :=
          (extend_eq (m := fun S (_hS : IsLeftHalfOpenBox S) => m S)
            (show IsLeftHalfOpenBox (T n) from hT n)).symm
  rw [lambdaStar_eq_iInf_boxCovers A, ← hinduced_eq_boxes]

end Extension

/-! ## 6. Borel sets -/

section Borel

/-- The Borel σ-algebra of a topological space. -/
abbrev borelSigmaAlgebra (α : Type*) [TopologicalSpace α] : MeasurableSpace α :=
  borel α

/-- Borel sets in Euclidean space are Lebesgue measurable. -/
theorem borelSet_lebesgueMeasurable {d : ℕ} {A : Set (Space d)}
    (hA : MeasurableSet A) :
    LebesgueMeasurableSet A := by
  exact hA.nullMeasurableSet

/--
The Borel measure on `ℝ^d`.

Mathlib's `volume` is used here.  Lebesgue measurable sets are represented in
Chapter 05 by `NullMeasurableSet A volume`, i.e. by the completion of this
Borel measure.
-/
abbrev borelMeasure (d : ℕ) : Measure (Space d) :=
  volume

theorem lebesgueMeasure_completion_of_borel {d : ℕ} {A : Set (Space d)} :
    LebesgueMeasurableSet A ↔
      CompletedMeasurableSet (borelMeasure d) A := by
  rfl

theorem lebesgueMeasurable_exists_borel_ae_eq {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) :
    ∃ B : Set (Space d), MeasurableSet B ∧ B =ᵐ[(volume : Measure (Space d))] A := by
  rcases hA.exists_measurable_superset_ae_eq with ⟨B, _hAB, hB, hBAe⟩
  exact ⟨B, hB, hBAe⟩

theorem lebesgueMeasurable_exists_borel_symmDiff_null {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) :
    ∃ B : Set (Space d), MeasurableSet B ∧ lambdaStar (symmDiff A B) = 0 := by
  rcases lebesgueMeasurable_exists_borel_ae_eq (d := d) hA with ⟨B, hB, hBAe⟩
  refine ⟨B, hB, ?_⟩
  have hzero : (volume : Measure (Space d)) (symmDiff B A) = 0 :=
    (measure_symmDiff_eq_zero_iff).2 hBAe
  simpa [lambdaStar, symmDiff_comm] using hzero

end Borel

/-!
## 7. Limits of Lebesgue measurability

The active lecture file treats Vitali sets, Solovay's model, Banach--Tarski,
and arbitrary additivity as expository context.  We intentionally do not add
formal statements here yet; the measure-theory development after Chapter 06
does not depend on them.
-/

end Chapter06
end NoteKsk
