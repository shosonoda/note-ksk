/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«02jordan»

/-!
# Chapter 03: Lebesgue outer measure

This file follows `blueprint/src/chapters/03lebesgue-outer.tex`.

The lecture note first defines Lebesgue outer measure by countable coverings with
left half-open rectangles.  In mathlib, Lebesgue measure is already available as
`volume`; applying a measure to an arbitrary set gives its outer-measure value.
We therefore use

* `Fin d → ℝ` as the model of `ℝ^d`;
* `(volume : Measure (Fin d → ℝ))` as Lebesgue outer measure on all subsets;
* explicit boxes and cover-cost definitions to keep the blueprint definition visible.

Statements depending on the Jordan theory of Chapter 2 import their definitions
and bridge theorems from `NoteKsk/02jordan.lean`.
-/

noncomputable section

open scoped BigOperators Topology
open Set MeasureTheory

namespace NoteKsk
namespace Chapter03

/-! ## 1. Lebesgue outer measure -/

/-- Bundled Lebesgue outer measure on `ℝ^d`. -/
abbrev lebesgueOuterMeasure (d : ℕ) : OuterMeasure (Space d) :=
  (volume : Measure (Space d)).toOuterMeasure

/--
Lebesgue outer measure `λ*`.

In mathlib this is simply Lebesgue measure `volume` evaluated on an arbitrary set.
For measurable sets it is the usual measure; for nonmeasurable sets it is the
corresponding outer-measure value.
-/
abbrev lambdaStar {d : ℕ} (A : Set (Space d)) : ENNReal :=
  (volume : Measure (Space d)) A

/-- A covering piece is either a left half-open box or the explicitly allowed empty set. -/
inductive CoverBox (d : ℕ) where
  | empty : CoverBox d
  | box : Box d → CoverBox d

namespace CoverBox

variable {d : ℕ}

/-- The set carried by a covering piece. -/
def carrier : CoverBox d → Set (Space d)
  | empty => ∅
  | box Q => Q.Ioc

/-- The volume of a covering piece. -/
def volume : CoverBox d → ENNReal
  | empty => 0
  | box Q => Q.volume

/-- Each covering piece has outer measure bounded by its declared volume. -/
theorem lambdaStar_carrier_le_volume (R : CoverBox d) :
    lambdaStar R.carrier ≤ R.volume := by
  cases R with
  | empty =>
      simp [carrier, volume, lambdaStar]
  | box Q =>
      simp [carrier, volume, lambdaStar, Box.Ioc, Box.volume, Real.volume_pi_Ioc]

end CoverBox

/-- A sequence of boxes covers `A`. -/
def IsBoxCover {d : ℕ} (A : Set (Space d)) (Q : ℕ → CoverBox d) : Prop :=
  A ⊆ ⋃ n, (Q n).carrier

/-- Cost of a countable box cover, `∑ n |Q_n|`. -/
def boxCoverCost {d : ℕ} (Q : ℕ → CoverBox d) : ENNReal :=
  ∑' n, (Q n).volume

/--
The blueprint definition: infimum of costs over all countable covers by left
half-open boxes.
-/
def lambdaStarByBoxes {d : ℕ} (A : Set (Space d)) : ENNReal :=
  ⨅ Q : ℕ → CoverBox d, ⨅ _hQ : IsBoxCover A Q, boxCoverCost Q

/--
The easy direction of the box-cover definition: every countable box cover gives
an upper bound for `λ* A`.
-/
theorem lambdaStar_le_lambdaStarByBoxes {d : ℕ} (A : Set (Space d)) :
    lambdaStar A ≤ lambdaStarByBoxes A := by
  refine le_iInf ?_
  intro Q
  refine le_iInf ?_
  intro hQ
  calc
    lambdaStar A ≤ lambdaStar (⋃ n, (Q n).carrier) :=
      measure_mono hQ
    _ ≤ ∑' n, lambdaStar ((Q n).carrier) :=
      by
        simpa [lambdaStar] using
          (measure_iUnion_le (μ := (volume : Measure (Space d)))
            (fun n => (Q n).carrier))
    _ ≤ boxCoverCost Q :=
      ENNReal.tsum_le_tsum fun n => CoverBox.lambdaStar_carrier_le_volume (Q n)

/--
The hard direction of the box-cover definition.  This is the part corresponding
to constructing Lebesgue outer measure from countable rectangle covers.  It is
kept as a TODO until the rectangle-cover construction is developed in full.
-/
theorem lambdaStarByBoxes_le_lambdaStar {d : ℕ} (A : Set (Space d)) :
    lambdaStarByBoxes A ≤ lambdaStar A := by
  sorry

/--
The box-cover definition agrees with mathlib's Lebesgue outer measure.

This is the formal version of the definition in the lecture notes.  The
nontrivial construction direction is isolated in
`lambdaStarByBoxes_le_lambdaStar`.
-/
theorem lambdaStar_eq_iInf_boxCovers {d : ℕ} (A : Set (Space d)) :
    lambdaStar A = lambdaStarByBoxes A := by
  exact le_antisymm (lambdaStar_le_lambdaStarByBoxes A) (lambdaStarByBoxes_le_lambdaStar A)

/-! ## 2. Outer-measure axioms -/

/-- Unbundled outer-measure axioms for comparison with the text. -/
def IsOuterMeasureFunction {α : Type*} (μ : Set α → ENNReal) : Prop :=
  μ ∅ = 0 ∧
    (∀ ⦃A B : Set α⦄, A ⊆ B → μ A ≤ μ B) ∧
    (∀ A : ℕ → Set α, μ (⋃ n, A n) ≤ ∑' n, μ (A n))

@[simp]
theorem lambdaStar_empty {d : ℕ} :
    lambdaStar (∅ : Set (Space d)) = 0 := by
  simp [lambdaStar]

theorem lambdaStar_mono {d : ℕ} {A B : Set (Space d)} (hAB : A ⊆ B) :
    lambdaStar A ≤ lambdaStar B := by
  exact measure_mono hAB

theorem lambdaStar_iUnion_le {d : ℕ} (A : ℕ → Set (Space d)) :
    lambdaStar (⋃ n, A n) ≤ ∑' n, lambdaStar (A n) := by
  simpa [lambdaStar] using
    (measure_iUnion_le (μ := (volume : Measure (Space d))) A)

theorem lambdaStar_union_le {d : ℕ} (A B : Set (Space d)) :
    lambdaStar (A ∪ B) ≤ lambdaStar A + lambdaStar B := by
  simpa [lambdaStar] using
    (measure_union_le (μ := (volume : Measure (Space d))) A B)

/-- `λ*` is a Carathéodory outer measure in the unbundled sense of the notes. -/
theorem lambdaStar_isOuterMeasureFunction (d : ℕ) :
    IsOuterMeasureFunction (fun A : Set (Space d) => lambdaStar A) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro A B hAB
    exact lambdaStar_mono hAB
  · intro A
    exact lambdaStar_iUnion_le A

/-! ## 3. Concrete computations and estimates -/

theorem lambdaStar_boxIoo {d : ℕ} (Q : Box d) :
    lambdaStar Q.Ioo = Q.volume := by
  simpa [lambdaStar, Box.Ioo, Box.volume] using
    (Real.volume_pi_Ioo (a := Q.lower) (b := Q.upper))

theorem lambdaStar_boxIoc {d : ℕ} (Q : Box d) :
    lambdaStar Q.Ioc = Q.volume := by
  simpa [lambdaStar, Box.Ioc, Box.volume] using
    (Real.volume_pi_Ioc (a := Q.lower) (b := Q.upper))

theorem lambdaStar_boxIco {d : ℕ} (Q : Box d) :
    lambdaStar Q.Ico = Q.volume := by
  simpa [lambdaStar, Box.Ico, Box.volume] using
    (Real.volume_pi_Ico (a := Q.lower) (b := Q.upper))

theorem lambdaStar_boxIcc {d : ℕ} (Q : Box d) :
    lambdaStar Q.Icc = Q.volume := by
  simpa [lambdaStar, Box.Icc, Box.volume] using
    (Real.volume_Icc_pi (a := Q.lower) (b := Q.upper))

/-- If `A` is covered by one left half-open box, `λ*(A) ≤ |Q|`. -/
theorem lambdaStar_le_boxVolume_of_subset {d : ℕ} {A : Set (Space d)} {Q : Box d}
    (hA : A ⊆ Q.Ioc) :
    lambdaStar A ≤ Q.volume := by
  calc
    lambdaStar A ≤ lambdaStar Q.Ioc := lambdaStar_mono hA
    _ = Q.volume := lambdaStar_boxIoc Q

/-- Bounded subsets of `ℝ^d` have finite Lebesgue outer measure. -/
theorem lambdaStar_lt_top_of_isBounded {d : ℕ} {A : Set (Space d)}
    (hA : Bornology.IsBounded A) :
    lambdaStar A < ⊤ := by
  simpa [lambdaStar] using
    (hA.measure_lt_top (μ := (volume : Measure (Space d))))

/--
One-point sets are null in positive dimension.

The assumption `[Nonempty (Fin d)]` excludes the degenerate `ℝ^0`, whose whole
space is a singleton.
-/
theorem lambdaStar_singleton {d : ℕ} [Nonempty (Fin d)] (a : Space d) :
    lambdaStar ({a} : Set (Space d)) = 0 := by
  simp [lambdaStar]

/-- Countable subsets of positive-dimensional Euclidean space are null. -/
theorem lambdaStar_countable_eq_zero {d : ℕ} [Nonempty (Fin d)]
    {A : Set (Space d)} (hA : A.Countable) :
    lambdaStar A = 0 := by
  simpa [lambdaStar] using
    (Set.Countable.measure_zero hA (volume : Measure (Space d)))

/-! ## 4. Translation invariance -/

/-- Lebesgue outer measure is invariant under translations. -/
theorem lambdaStar_translate {d : ℕ} (A : Set (Space d)) (c : Space d) :
    lambdaStar (translate A c) = lambdaStar A := by
  have hpre :
      (fun x : Space d => x + c) ⁻¹' translate A c = A := by
    ext x
    simp [translate]
  have h :=
    measure_preimage_add_right (volume : Measure (Space d)) c (translate A c)
  rw [hpre] at h
  simpa [lambdaStar] using h.symm

/-! ## 5. Jordan-measure compatibility -/

/--
Lebesgue outer measure is bounded above by Jordan outer measure on bounded sets.
This is a Chapter 2 compatibility statement.
-/
theorem lambdaStar_le_jordanOuterMeasure {d : ℕ} {A : Set (Space d)}
    (_hA : Bornology.IsBounded A) :
    lambdaStar A ≤ jordanOuterMeasure A := by
  refine le_iInf ?_
  intro E
  refine le_iInf ?_
  intro _hE
  refine le_iInf ?_
  intro hAE
  simpa [lambdaStar, elementaryVolume] using
    (measure_mono (μ := (volume : Measure (Space d))) hAE)

/--
On Jordan measurable sets, Jordan measure and Lebesgue outer measure agree.
This is a Chapter 2 compatibility statement.
-/
theorem jordanMeasure_eq_lambdaStar {d : ℕ} {A : Set (Space d)}
    (hA : JordanMeasurable A) :
    jordanMeasure A = lambdaStar A := by
  simpa [lambdaStar] using
    (Chapter02.jordanMeasure_eq_volume_of_jordanMeasurable (d := d) (A := A) hA)

/--
Countable additivity of `λ*` on pairwise disjoint Jordan measurable sets.
This is a Chapter 2 compatibility statement.
-/
theorem lambdaStar_iUnion_eq_tsum_of_jordanMeasurable {d : ℕ}
    (A : ℕ → Set (Space d))
    (hdisj : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (A m) (A n))
    (hA : ∀ n, JordanMeasurable (A n)) :
    lambdaStar (⋃ n, A n) = ∑' n, lambdaStar (A n) := by
  simpa [lambdaStar] using
    (Chapter02.volume_iUnion_eq_tsum_of_jordanMeasurable (d := d) A hdisj hA)

/-! ## 6. Outer regularity by open supersets -/

/-- Infimum of `λ*(G)` over open supersets `G ⊇ A`. -/
def lambdaStarByOpenSupersets {d : ℕ} (A : Set (Space d)) : ENNReal :=
  ⨅ G : Set (Space d), ⨅ _hAG : A ⊆ G, ⨅ _hG : IsOpen G, lambdaStar G

/-- Lebesgue outer measure is outer regular: approximate from above by open sets. -/
theorem lambdaStar_outerRegular_open {d : ℕ} (A : Set (Space d)) :
    lambdaStar A = lambdaStarByOpenSupersets A := by
  simpa [lambdaStarByOpenSupersets, lambdaStar] using
    (Set.measure_eq_iInf_isOpen (A := A) (μ := (volume : Measure (Space d))))

/-! ## 7. Auxiliary outer-measure lemmas -/

/-- Two sets are separated by a positive distance. -/
def PositiveDistanceApart {d : ℕ} (A B : Set (Space d)) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → δ ≤ dist a b

/-- Lebesgue outer measure is additive on sets separated by positive distance. -/
theorem lambdaStar_union_of_positiveDistanceApart {d : ℕ}
    {A B : Set (Space d)} (hsep : PositiveDistanceApart A B) :
    lambdaStar (A ∪ B) = lambdaStar A + lambdaStar B := by
  rcases hsep with ⟨δ, hδpos, hδ⟩
  let S : Set (Space d) := {x | ENNReal.ofReal (δ / 2) ≤ Metric.infEDist x B}
  have hhalf_pos : 0 < δ / 2 := by linarith
  have hSclosed : IsClosed S := by
    simpa [S] using
      (isClosed_Ici.preimage (Metric.continuous_infEDist (s := B)))
  have hA_subset_S : A ⊆ S := by
    intro a ha
    dsimp [S]
    rw [Metric.le_infEDist]
    intro b hb
    have hhalf_le : δ / 2 ≤ dist a b := by
      linarith [hδ ha hb]
    simpa [edist_dist] using ENNReal.ofReal_le_ofReal hhalf_le
  have hB_subset_compl : B ⊆ Sᶜ := by
    intro b hb hbS
    have hpos : 0 < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr hhalf_pos
    have hzero : Metric.infEDist b B = 0 := Metric.infEDist_zero_of_mem hb
    exact (not_le_of_gt hpos) (by simpa [S, hzero] using hbS)
  have h_inter : (A ∪ B) ∩ S = A := by
    ext x
    constructor
    · rintro ⟨hxAB, hxS⟩
      rcases hxAB with hxA | hxB
      · exact hxA
      · exact False.elim ((hB_subset_compl hxB) hxS)
    · intro hxA
      exact ⟨Or.inl hxA, hA_subset_S hxA⟩
  have h_diff : (A ∪ B) \ S = B := by
    ext x
    constructor
    · rintro ⟨hxAB, hxS⟩
      rcases hxAB with hxA | hxB
      · exact False.elim (hxS (hA_subset_S hxA))
      · exact hxB
    · intro hxB
      exact ⟨Or.inr hxB, hB_subset_compl hxB⟩
  have hsplit :=
    measure_inter_add_diff (μ := (volume : Measure (Space d))) (s := A ∪ B) hSclosed.measurableSet
  simpa [lambdaStar, h_inter, h_diff] using hsplit.symm

/--
Finite-measure open sets can be approximated from inside by compact sets.
The `ENNReal` form avoids subtracting an epsilon from an extended value.
-/
theorem finiteOpen_innerCompact_exists {d : ℕ}
    {U : Set (Space d)} (hUopen : IsOpen U) (hUfin : lambdaStar U < ⊤)
    {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ K : Set (Space d),
      IsCompact K ∧ K ⊆ U ∧ lambdaStar U ≤ lambdaStar K + ε := by
  rcases hUopen.measurableSet.exists_isCompact_lt_add
      (μ := (volume : Measure (Space d)))
      (by simpa [lambdaStar] using hUfin.ne) hε with ⟨K, hKU, hK, hKμ⟩
  exact ⟨K, hK, hKU, le_of_lt (by simpa [lambdaStar] using hKμ)⟩

/-- Splitting a finite-measure open set by a compact set. -/
theorem finiteOpen_compact_split {d : ℕ}
    {O K : Set (Space d)}
    (_hOopen : IsOpen O) (_hOfin : lambdaStar O < ⊤) (hK : IsCompact K) :
    lambdaStar O = lambdaStar (O ∩ K) + lambdaStar (O \ K) := by
  simpa [lambdaStar] using
    (measure_inter_add_diff (μ := (volume : Measure (Space d))) (s := O) hK.measurableSet).symm

/-- Compact sets split Lebesgue outer measure of arbitrary sets. -/
theorem compact_splits_lambdaStar {d : ℕ}
    {C B : Set (Space d)} (hC : IsCompact C) :
    lambdaStar B = lambdaStar (B ∩ C) + lambdaStar (B \ C) := by
  simpa [lambdaStar] using
    (measure_inter_add_diff (μ := (volume : Measure (Space d))) (s := B) hC.measurableSet).symm

end Chapter03
end NoteKsk
