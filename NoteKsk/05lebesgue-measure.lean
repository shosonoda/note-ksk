/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«04lebesgue-inner»

/-!
# Chapter 05: Lebesgue measurable sets and Lebesgue measure

This file follows the active blueprint file
`blueprint/src/chapters/05lebesgue03.tex`.

We use mathlib's completed measurable-set predicate `NullMeasurableSet` for
Lebesgue measurable sets.  The chapter-specific inner/outer measure criteria
are recorded as derived theorems, so later files can use the lecture-note names
while the closure and additivity results are proved by the existing measure API.
-/

noncomputable section

open scoped BigOperators Topology
open Set MeasureTheory

namespace NoteKsk
open Chapter03 Chapter04

namespace Chapter05

/-! ## 1. Lebesgue measurability and measure -/

/-- Lebesgue measurable subsets of `ℝ^d`, represented by null-measurable sets for `volume`. -/
def LebesgueMeasurableSet {d : ℕ} (A : Set (Space d)) : Prop :=
  NullMeasurableSet A (volume : Measure (Space d))

/-- Lebesgue measure is the restriction of outer measure to measurable sets. -/
def lebesgueMeasure {d : ℕ} (A : Set (Space d)) : ENNReal :=
  lambdaStar A

/-- Lebesgue null sets are sets of outer measure zero. -/
def LebesgueNullSet {d : ℕ} (A : Set (Space d)) : Prop :=
  lambdaStar A = 0

theorem lebesgueMeasurableSet_iff_nullMeasurable {d : ℕ} {A : Set (Space d)} :
    LebesgueMeasurableSet A ↔ NullMeasurableSet A (volume : Measure (Space d)) := by
  rfl

theorem lebesgueMeasure_eq_lambdaStar {d : ℕ} (A : Set (Space d)) :
    lebesgueMeasure A = lambdaStar A := by
  rfl

private theorem measurableSet_boxIcc {d : ℕ} (Q : Box d) :
    MeasurableSet Q.Icc := by
  simp [Box.Icc]

private theorem measurableSet_closedCube {d : ℕ} (R : ℝ) :
    MeasurableSet (closedCube d R) := by
  simpa [closedCube] using measurableSet_boxIcc (closedCubeBox d R)

private theorem isCompact_closedCube {d : ℕ} (R : ℝ) :
    IsCompact (closedCube d R) := by
  simpa [closedCube, Box.Icc] using
    (isCompact_Icc : IsCompact (Set.Icc (closedCubeBox d R).lower (closedCubeBox d R).upper))

/-- Lebesgue measurable sets have equal inner and outer measure. -/
theorem lebesgueMeasurableSet_inner_eq_outer {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) :
    lambdaInner A = lambdaStar A := by
  refine le_antisymm (lambdaInner_le_lambdaStar A) ?_
  rcases hA.exists_measurable_subset_ae_eq with ⟨B, hBA, hBmeas, hBAe⟩
  calc
    lambdaStar A = lambdaStar B := by
      simpa [lambdaStar] using (measure_congr hBAe).symm
    _ = lambdaInner B := (lambdaInner_eq_lambdaStar_of_measurableSet hBmeas).symm
    _ ≤ lambdaInner A := lambdaInner_mono hBA

/--
Window form used in the lecture notes: every bounded cube sees equality of
inner and outer measure.
-/
theorem lebesgueMeasurableSet_windows {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) :
    ∀ R : ℝ, 0 < R →
      lambdaInner (A ∩ closedCube d R) = lambdaStar (A ∩ closedCube d R) := by
  intro R _hR
  exact lebesgueMeasurableSet_inner_eq_outer
    (hA.inter (measurableSet_closedCube (d := d) R).nullMeasurableSet)

/--
For finite outer measure, measurability implies the global inner/outer equality.
The converse is the constructive criterion developed in the notes; the usable
direction needed downstream is this implication.
-/
theorem finiteOuter_lebesgueMeasurable_inner_eq_outer {d : ℕ}
    {A : Set (Space d)} (_hAfin : lambdaStar A < ⊤) :
    LebesgueMeasurableSet A → lambdaInner A = lambdaStar A :=
  lebesgueMeasurableSet_inner_eq_outer

/-- Bounded measurable sets split the containing closed box. -/
theorem boundedMeasurable_intervalCriterion {d : ℕ}
    (Q : Box d) {A : Set (Space d)}
    (hAQ : A ⊆ Q.Icc) (hA : LebesgueMeasurableSet A) :
    Q.volume = lambdaStar A + lambdaStar (Q.Icc \ A) := by
  have hsplit :=
    measure_inter_add_diff₀ (μ := (volume : Measure (Space d))) (s := Q.Icc) hA
  have h_inter : Q.Icc ∩ A = A := Set.inter_eq_self_of_subset_right hAQ
  simpa [lambdaStar, lambdaStar_boxIcc Q, h_inter] using hsplit.symm

/-! ## 2. Basic examples -/

theorem lebesgueNullSet_measurable {d : ℕ} {N : Set (Space d)}
    (hN : LebesgueNullSet N) :
    LebesgueMeasurableSet N := by
  exact NullMeasurableSet.of_null
    (μ := (volume : Measure (Space d))) (by simpa [LebesgueNullSet, lambdaStar] using hN)

theorem lebesgueMeasure_eq_zero_of_null {d : ℕ} {N : Set (Space d)}
    (hN : LebesgueNullSet N) :
    lebesgueMeasure N = 0 := by
  simpa [lebesgueMeasure, LebesgueNullSet] using hN

theorem countable_lebesgueMeasurable {d : ℕ} [Nonempty (Fin d)]
    {A : Set (Space d)} (hA : A.Countable) :
    LebesgueMeasurableSet A := by
  exact lebesgueNullSet_measurable
    (d := d) (N := A) (Chapter03.lambdaStar_countable_eq_zero (d := d) hA)

theorem countable_lebesgueMeasure_eq_zero {d : ℕ} [Nonempty (Fin d)]
    {A : Set (Space d)} (hA : A.Countable) :
    lebesgueMeasure A = 0 := by
  exact lebesgueMeasure_eq_zero_of_null
    (d := d) (N := A) (Chapter03.lambdaStar_countable_eq_zero (d := d) hA)

theorem jordanMeasurable_lebesgueMeasurable {d : ℕ} {A : Set (Space d)}
    (hA : JordanMeasurable A) :
    LebesgueMeasurableSet A := by
  exact hA.2.1.nullMeasurableSet

theorem lebesgueMeasure_eq_jordanMeasure {d : ℕ} {A : Set (Space d)}
    (hA : JordanMeasurable A) :
    lebesgueMeasure A = jordanMeasure A := by
  simpa [lebesgueMeasure] using
    (Chapter03.jordanMeasure_eq_lambdaStar (d := d) (A := A) hA).symm

/-! ## 3. Finite outer-measure approximation criteria -/

theorem finiteOuter_compact_approx_criterion {d : ℕ}
    {A : Set (Space d)} (hAfin : lambdaStar A < ⊤)
    (hA : LebesgueMeasurableSet A) :
    ∀ ε : ENNReal, ε ≠ 0 →
      ∃ K : Set (Space d), IsCompact K ∧ K ⊆ A ∧ lambdaStar (A \ K) < ε := by
  intro ε hε
  rcases hA.exists_measurable_subset_ae_eq with ⟨B, hBA, hBmeas, hBAe⟩
  have hBfin : (volume : Measure (Space d)) B ≠ ⊤ := by
    rw [measure_congr hBAe]
    exact ne_top_of_lt hAfin
  rcases hBmeas.exists_isCompact_diff_lt hBfin hε with ⟨K, hKB, hK, hlt⟩
  refine ⟨K, hK, hKB.trans hBA, ?_⟩
  have hdiff :
      (volume : Measure (Space d)) (A \ K) =
        (volume : Measure (Space d)) (B \ K) := by
    exact (measure_congr
      (hBAe.diff (ae_eq_refl K))).symm
  simpa [lambdaStar, hdiff] using hlt

theorem finiteOuter_open_approx_criterion {d : ℕ}
    {A : Set (Space d)} (hAfin : lambdaStar A < ⊤)
    (hA : LebesgueMeasurableSet A) :
    ∀ ε : ENNReal, ε ≠ 0 →
      ∃ U : Set (Space d), A ⊆ U ∧ IsOpen U ∧ lambdaStar (U \ A) < ε := by
  intro ε hε
  rcases hA.exists_measurable_superset_ae_eq with ⟨B, hAB, hBmeas, hBAe⟩
  have hBfin : (volume : Measure (Space d)) B ≠ ⊤ := by
    rw [measure_congr hBAe]
    exact ne_top_of_lt hAfin
  rcases hBmeas.exists_isOpen_diff_lt hBfin hε with ⟨U, hBU, hUopen, _hUfin, hlt⟩
  refine ⟨U, hAB.trans hBU, hUopen, ?_⟩
  have hdiff :
      (volume : Measure (Space d)) (U \ A) =
        (volume : Measure (Space d)) (U \ B) := by
    exact (measure_congr
      ((ae_eq_refl U).diff hBAe)).symm
  simpa [lambdaStar, hdiff] using hlt

/-! ## 4. Local measurable sets inside a closed box -/

/-- Measurability inside a bounded window `Q`, written `𝓛(Q)` in the notes. -/
def LocalLebesgueMeasurable {d : ℕ} (Q A : Set (Space d)) : Prop :=
  A ⊆ Q ∧ LebesgueMeasurableSet A

theorem localLebesgueMeasurable_iff {d : ℕ}
    {Q A : Set (Space d)} :
    LocalLebesgueMeasurable Q A ↔ A ⊆ Q ∧ LebesgueMeasurableSet A := by
  rfl

theorem localLebesgueMeasurable_compl {d : ℕ}
    (Q : Box d) {A : Set (Space d)}
    (hA : LocalLebesgueMeasurable Q.Icc A) :
    LocalLebesgueMeasurable Q.Icc (Q.Icc \ A) := by
  refine ⟨Set.diff_subset, ?_⟩
  exact (measurableSet_boxIcc Q).nullMeasurableSet.diff hA.2

theorem localLebesgueMeasurable_union {d : ℕ}
    (Q : Box d) {A B : Set (Space d)}
    (hA : LocalLebesgueMeasurable Q.Icc A)
    (hB : LocalLebesgueMeasurable Q.Icc B) :
    LocalLebesgueMeasurable Q.Icc (A ∪ B) := by
  exact ⟨Set.union_subset hA.1 hB.1, hA.2.union hB.2⟩

theorem localLebesgueMeasurable_union_additive {d : ℕ}
    (_Q : Box d) {A B : Set (Space d)}
    (_hA : LocalLebesgueMeasurable _Q.Icc A)
    (hB : LocalLebesgueMeasurable _Q.Icc B)
    (hdisj : Disjoint A B) :
    lambdaStar (A ∪ B) = lambdaStar A + lambdaStar B := by
  simpa [lambdaStar] using
    (measure_union₀ (μ := (volume : Measure (Space d))) hB.2 hdisj.aedisjoint)

theorem localLebesgueMeasurable_inter {d : ℕ}
    (Q : Box d) {A B : Set (Space d)}
    (hA : LocalLebesgueMeasurable Q.Icc A)
    (hB : LocalLebesgueMeasurable Q.Icc B) :
    LocalLebesgueMeasurable Q.Icc (A ∩ B) := by
  exact ⟨Set.Subset.trans Set.inter_subset_left hA.1, hA.2.inter hB.2⟩

theorem localLebesgueMeasurable_diff {d : ℕ}
    (Q : Box d) {A B : Set (Space d)}
    (hA : LocalLebesgueMeasurable Q.Icc A)
    (hB : LocalLebesgueMeasurable Q.Icc B) :
    LocalLebesgueMeasurable Q.Icc (A \ B) := by
  exact ⟨Set.Subset.trans Set.diff_subset hA.1, hA.2.diff hB.2⟩

theorem localLebesgueMeasurable_iUnion {d : ℕ}
    (Q : Box d) (A : ℕ → Set (Space d))
    (hA : ∀ n, LocalLebesgueMeasurable Q.Icc (A n)) :
    LocalLebesgueMeasurable Q.Icc (⋃ n, A n) := by
  exact ⟨Set.iUnion_subset fun n => (hA n).1, NullMeasurableSet.iUnion fun n => (hA n).2⟩

theorem localLebesgueMeasurable_iUnion_additive {d : ℕ}
    (_Q : Box d) (A : ℕ → Set (Space d))
    (hA : ∀ n, LocalLebesgueMeasurable _Q.Icc (A n))
    (hdisj : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (A m) (A n)) :
    lambdaStar (⋃ n, A n) = ∑' n, lambdaStar (A n) := by
  have hpair : Pairwise (Function.onFun (AEDisjoint (volume : Measure (Space d))) A) := by
    intro m n hmn
    exact (hdisj hmn).aedisjoint
  simpa [lambdaStar] using
    (measure_iUnion₀ (μ := (volume : Measure (Space d))) hpair fun n => (hA n).2)

/-! ## 5. Global closure properties -/

theorem lebesgueMeasurableSet_univ {d : ℕ} :
    LebesgueMeasurableSet (Set.univ : Set (Space d)) := by
  exact nullMeasurableSet_univ

theorem lebesgueMeasurableSet_empty {d : ℕ} :
    LebesgueMeasurableSet (∅ : Set (Space d)) := by
  exact nullMeasurableSet_empty

theorem lebesgueMeasurableSet_compl {d : ℕ} {A : Set (Space d)}
    (hA : LebesgueMeasurableSet A) :
    LebesgueMeasurableSet Aᶜ := by
  exact hA.compl

theorem lebesgueMeasurableSet_iUnion {d : ℕ}
    (A : ℕ → Set (Space d)) (hA : ∀ n, LebesgueMeasurableSet (A n)) :
    LebesgueMeasurableSet (⋃ n, A n) := by
  exact NullMeasurableSet.iUnion hA

theorem lebesgueMeasurableSet_union {d : ℕ}
    {A B : Set (Space d)}
    (hA : LebesgueMeasurableSet A) (hB : LebesgueMeasurableSet B) :
    LebesgueMeasurableSet (A ∪ B) := by
  exact hA.union hB

theorem lebesgueMeasurableSet_inter {d : ℕ}
    {A B : Set (Space d)}
    (hA : LebesgueMeasurableSet A) (hB : LebesgueMeasurableSet B) :
    LebesgueMeasurableSet (A ∩ B) := by
  exact hA.inter hB

theorem lebesgueMeasurableSet_diff {d : ℕ}
    {A B : Set (Space d)}
    (hA : LebesgueMeasurableSet A) (hB : LebesgueMeasurableSet B) :
    LebesgueMeasurableSet (A \ B) := by
  exact hA.diff hB

theorem lebesgueMeasurableSet_iInter {d : ℕ}
    (A : ℕ → Set (Space d)) (hA : ∀ n, LebesgueMeasurableSet (A n)) :
    LebesgueMeasurableSet (⋂ n, A n) := by
  exact NullMeasurableSet.iInter hA

theorem isClosed_lebesgueMeasurable {d : ℕ} {F : Set (Space d)}
    (hF : IsClosed F) :
    LebesgueMeasurableSet F := by
  exact hF.measurableSet.nullMeasurableSet

theorem isOpen_lebesgueMeasurable {d : ℕ} {G : Set (Space d)}
    (hG : IsOpen G) :
    LebesgueMeasurableSet G := by
  exact hG.measurableSet.nullMeasurableSet

/-! ## 6. Lebesgue measure -/

theorem lebesgueMeasure_empty {d : ℕ} :
    lebesgueMeasure (∅ : Set (Space d)) = 0 := by
  simp [lebesgueMeasure]

theorem lebesgueMeasure_nonneg {d : ℕ} (A : Set (Space d)) :
    0 ≤ lebesgueMeasure A := by
  exact bot_le

theorem lebesgueMeasure_mono {d : ℕ} {A B : Set (Space d)}
    (_hA : LebesgueMeasurableSet A) (_hB : LebesgueMeasurableSet B)
    (hAB : A ⊆ B) :
    lebesgueMeasure A ≤ lebesgueMeasure B := by
  simpa [lebesgueMeasure] using Chapter03.lambdaStar_mono hAB

theorem lebesgueMeasure_union_add {d : ℕ} {A B : Set (Space d)}
    (_hA : LebesgueMeasurableSet A) (hB : LebesgueMeasurableSet B)
    (hdisj : Disjoint A B) :
    lebesgueMeasure (A ∪ B) = lebesgueMeasure A + lebesgueMeasure B := by
  simpa [lebesgueMeasure, lambdaStar] using
    (measure_union₀ (μ := (volume : Measure (Space d))) hB hdisj.aedisjoint)

theorem lebesgueMeasure_iUnion_eq_tsum {d : ℕ}
    (A : ℕ → Set (Space d))
    (hA : ∀ n, LebesgueMeasurableSet (A n))
    (hdisj : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (A m) (A n)) :
    lebesgueMeasure (⋃ n, A n) = ∑' n, lebesgueMeasure (A n) := by
  have hpair : Pairwise (Function.onFun (AEDisjoint (volume : Measure (Space d))) A) := by
    intro m n hmn
    exact (hdisj hmn).aedisjoint
  simpa [lebesgueMeasure, lambdaStar] using
    (measure_iUnion₀ (μ := (volume : Measure (Space d))) hpair hA)

theorem lebesgueMeasure_iUnion_le_tsum {d : ℕ}
    (A : ℕ → Set (Space d)) (_hA : ∀ n, LebesgueMeasurableSet (A n)) :
    lebesgueMeasure (⋃ n, A n) ≤ ∑' n, lebesgueMeasure (A n) := by
  simpa [lebesgueMeasure] using Chapter03.lambdaStar_iUnion_le A

theorem lebesgueMeasure_iUnion_eq_iSup_of_mono {d : ℕ}
    (A : ℕ → Set (Space d))
    (_hA : ∀ n, LebesgueMeasurableSet (A n))
    (hmono : ∀ n, A n ⊆ A (n + 1)) :
    lebesgueMeasure (⋃ n, A n) = ⨆ n, lebesgueMeasure (A n) := by
  have hmono' : Monotone A := monotone_nat_of_le_succ hmono
  simpa [lebesgueMeasure, lambdaStar] using
    (hmono'.measure_iUnion (μ := (volume : Measure (Space d))))

theorem lebesgueMeasure_iInter_eq_iInf_of_antitone {d : ℕ}
    (A : ℕ → Set (Space d))
    (hA : ∀ n, LebesgueMeasurableSet (A n))
    (hmono : ∀ n, A (n + 1) ⊆ A n)
    (hfinite : lebesgueMeasure (A 0) < ⊤) :
    lebesgueMeasure (⋂ n, A n) = ⨅ n, lebesgueMeasure (A n) := by
  have hanti : Antitone A := antitone_nat_of_succ_le hmono
  have hfin : ∃ n, (volume : Measure (Space d)) (A n) ≠ ⊤ :=
    ⟨0, by simpa [lebesgueMeasure, lambdaStar] using ne_top_of_lt hfinite⟩
  simpa [lebesgueMeasure, lambdaStar] using
    (hanti.measure_iInter (μ := (volume : Measure (Space d))) hA hfin)

theorem lebesgueMeasurableSet_translate {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) (c : Space d) :
    LebesgueMeasurableSet (translate A c) := by
  have hpre : translate A c = (fun x : Space d => x - c) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hyA, rfl⟩
      simpa using hyA
    · intro hx
      exact ⟨x - c, hx, by simp [sub_eq_add_neg]⟩
  rw [hpre]
  simpa [sub_eq_add_neg] using
    hA.preimage
      ((measurePreserving_add_right (volume : Measure (Space d)) (-c)).quasiMeasurePreserving)

theorem lebesgueMeasure_translate {d : ℕ}
    (A : Set (Space d)) (c : Space d) :
    lebesgueMeasure (translate A c) = lebesgueMeasure A := by
  simpa [lebesgueMeasure] using Chapter03.lambdaStar_translate (d := d) A c

/-! ## 7. Regularity -/

theorem lebesgueMeasure_outerRegular {d : ℕ}
    {A : Set (Space d)} (_hA : LebesgueMeasurableSet A) :
    lebesgueMeasure A =
      ⨅ G : Set (Space d), ⨅ _hAG : A ⊆ G, ⨅ _hG : IsOpen G, lebesgueMeasure G := by
  simpa [lebesgueMeasure, lambdaStar] using
    (Set.measure_eq_iInf_isOpen (A := A) (μ := (volume : Measure (Space d))))

theorem lebesgueMeasure_innerRegular {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) :
    lebesgueMeasure A =
      ⨆ K : Set (Space d), ⨆ _hKA : K ⊆ A, ⨆ _hK : IsCompact K, lebesgueMeasure K := by
  rcases hA.exists_measurable_subset_ae_eq with ⟨B, hBA, hBmeas, hBAe⟩
  refine le_antisymm ?_ ?_
  · calc
      lebesgueMeasure A = lebesgueMeasure B := by
        simpa [lebesgueMeasure, lambdaStar] using (measure_congr hBAe).symm
      _ = ⨆ K : Set (Space d), ⨆ _hKB : K ⊆ B, ⨆ _hK : IsCompact K, lebesgueMeasure K := by
        simpa [lebesgueMeasure, lambdaStar] using
          (hBmeas.measure_eq_iSup_isCompact (μ := (volume : Measure (Space d))))
      _ ≤ ⨆ K : Set (Space d), ⨆ _hKA : K ⊆ A, ⨆ _hK : IsCompact K, lebesgueMeasure K := by
        refine iSup_le ?_
        intro K
        refine iSup_le ?_
        intro hKB
        refine iSup_le ?_
        intro hK
        exact le_iSup_of_le K <|
          le_iSup_of_le (hKB.trans hBA) <|
            le_iSup_of_le hK le_rfl
  · refine iSup_le ?_
    intro K
    refine iSup_le ?_
    intro hKA
    refine iSup_le ?_
    intro _hK
    simpa [lebesgueMeasure] using Chapter03.lambdaStar_mono hKA

/-! ## 8. Carathéodory criterion -/

/-- Carathéodory measurability for Lebesgue outer measure. -/
def LebesgueCaratheodoryMeasurable {d : ℕ} (A : Set (Space d)) : Prop :=
  ∀ E : Set (Space d),
    lambdaStar E = lambdaStar (E ∩ A) + lambdaStar (E \ A)

private theorem closedCube_iUnion_nat {d : ℕ} :
    (⋃ n : ℕ, closedCube d (n + 1 : ℝ)) = (Set.univ : Set (Space d)) := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    let S : ℝ := ∑ i : Fin d, |x i|
    obtain ⟨n, hn⟩ := exists_nat_gt S
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have hSle : S ≤ (n + 1 : ℝ) := by
      exact (le_of_lt hn).trans (by exact_mod_cast Nat.le_succ n)
    change x ∈ (closedCubeBox d (n + 1 : ℝ)).Icc
    change (closedCubeBox d (n + 1 : ℝ)).lower ≤ x ∧
      x ≤ (closedCubeBox d (n + 1 : ℝ)).upper
    constructor
    · intro i
      change -(n + 1 : ℝ) ≤ x i
      have hi : |x i| ≤ S := by
        exact Finset.single_le_sum (fun j _hj => abs_nonneg (x j)) (Finset.mem_univ i)
      have hlow := (abs_le.mp (hi.trans hSle)).1
      linarith
    · intro i
      change x i ≤ (n + 1 : ℝ)
      have hi : |x i| ≤ S := by
        exact Finset.single_le_sum (fun j _hj => abs_nonneg (x j)) (Finset.mem_univ i)
      exact (abs_le.mp (hi.trans hSle)).2

private theorem caratheodory_inter_finite_nullMeasurable {d : ℕ}
    {A C : Set (Space d)}
    (hA : LebesgueCaratheodoryMeasurable A)
    (hCmeas : MeasurableSet C)
    (hCfin : (volume : Measure (Space d)) C < ⊤) :
    LebesgueMeasurableSet (A ∩ C) := by
  let S : Set (Space d) := A ∩ C
  rcases exists_measurable_superset (volume : Measure (Space d)) S with
    ⟨M, hSM, hMmeas, hMμ⟩
  let E : Set (Space d) := M ∩ C
  have hEmeas : MeasurableSet E := hMmeas.inter hCmeas
  have hSE : S ⊆ E := by
    intro x hx
    exact ⟨hSM hx, hx.2⟩
  have hEμ : (volume : Measure (Space d)) E = (volume : Measure (Space d)) S := by
    refine le_antisymm ?_ (measure_mono hSE)
    calc
      (volume : Measure (Space d)) E ≤ (volume : Measure (Space d)) M :=
        measure_mono Set.inter_subset_left
      _ = (volume : Measure (Space d)) S := hMμ
  have hSfin : (volume : Measure (Space d)) S ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_lt hCfin) (measure_mono Set.inter_subset_right)
  have hEA : E ∩ A = S := by
    ext x
    constructor
    · rintro ⟨⟨_hxM, hxC⟩, hxA⟩
      exact ⟨hxA, hxC⟩
    · intro hx
      exact ⟨⟨hSM hx, hx.2⟩, hx.1⟩
  have hsplit :
      (volume : Measure (Space d)) E =
        (volume : Measure (Space d)) S + (volume : Measure (Space d)) (E \ A) := by
    simpa [LebesgueCaratheodoryMeasurable, lambdaStar, hEA] using hA E
  have hdiff_zero : (volume : Measure (Space d)) (E \ A) = 0 := by
    by_contra hdiff
    have hlt :
        (volume : Measure (Space d)) S <
          (volume : Measure (Space d)) S + (volume : Measure (Space d)) (E \ A) :=
      ENNReal.lt_add_right hSfin hdiff
    rw [← hsplit, hEμ] at hlt
    exact (lt_irrefl _ hlt)
  have hS_eq : S = E \ (E \ A) := by
    ext x
    constructor
    · intro hx
      exact ⟨hSE hx, fun hxEA => hxEA.2 hx.1⟩
    · rintro ⟨hxE, hxnot⟩
      refine ⟨?_, hxE.2⟩
      by_contra hxA
      exact hxnot ⟨hxE, hxA⟩
  rw [show A ∩ C = S by rfl, hS_eq]
  exact hEmeas.nullMeasurableSet.diff (NullMeasurableSet.of_null hdiff_zero)

theorem lebesgueMeasurable_caratheodory_finite {d : ℕ}
    {A E : Set (Space d)}
    (hA : LebesgueMeasurableSet A) (_hEfin : lambdaStar E < ⊤) :
    lambdaStar E = lambdaStar (E ∩ A) + lambdaStar (E \ A) := by
  simpa [lambdaStar] using
    (measure_inter_add_diff₀ (μ := (volume : Measure (Space d))) (s := E) hA).symm

theorem lebesgueMeasurable_implies_caratheodory {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueMeasurableSet A) :
    LebesgueCaratheodoryMeasurable A := by
  intro E
  simpa [lambdaStar] using
    (measure_inter_add_diff₀ (μ := (volume : Measure (Space d))) (s := E) hA).symm

theorem caratheodory_implies_lebesgueMeasurable {d : ℕ}
    {A : Set (Space d)} (hA : LebesgueCaratheodoryMeasurable A) :
    LebesgueMeasurableSet A := by
  have hpieces : ∀ n : ℕ, LebesgueMeasurableSet (A ∩ closedCube d (n + 1 : ℝ)) := by
    intro n
    exact caratheodory_inter_finite_nullMeasurable
      (A := A) (C := closedCube d (n + 1 : ℝ)) hA
      (measurableSet_closedCube (d := d) (n + 1 : ℝ))
      (by
        simpa [lambdaStar] using
          (isCompact_closedCube (d := d) (n + 1 : ℝ)).measure_lt_top
            (μ := (volume : Measure (Space d))))
  have hcover : A = ⋃ n : ℕ, A ∩ closedCube d (n + 1 : ℝ) := by
    rw [← Set.inter_iUnion, closedCube_iUnion_nat, Set.inter_univ]
  rw [hcover]
  exact NullMeasurableSet.iUnion hpieces

theorem lebesgueMeasurable_iff_caratheodory {d : ℕ}
    {A : Set (Space d)} :
    LebesgueMeasurableSet A ↔ LebesgueCaratheodoryMeasurable A := by
  constructor
  · exact lebesgueMeasurable_implies_caratheodory
  · exact caratheodory_implies_lebesgueMeasurable

end Chapter05
end NoteKsk
