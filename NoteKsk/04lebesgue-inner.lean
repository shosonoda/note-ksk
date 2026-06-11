/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«03lebesgue-outer»

/-!
# Chapter 04: Lebesgue inner measure

This file follows `blueprint/src/chapters/04lebesgue-inner.tex`.

The chapter introduces Lebesgue inner measure by compact subsets:

`λ_*(A) = sup { λ*(K) | K ⊆ A, K compact }`.

Basic order properties are proved directly from the definition.  The
outer-measure regularity and splitting lemmas used here are recorded in
Chapter 03.
-/

noncomputable section

open scoped BigOperators Topology
open Set MeasureTheory

namespace NoteKsk
open Chapter03

namespace Chapter04

/-! ## 1. Definition -/

/-- Lebesgue inner measure `λ_*`, defined by compact subsets. -/
def lambdaInner {d : ℕ} (A : Set (Space d)) : ENNReal :=
  ⨆ K : Set (Space d), ⨆ _hK : IsCompact K, ⨆ _hKA : K ⊆ A, lambdaStar K

/-! ## 2. Basic properties -/

theorem lambdaInner_nonneg {d : ℕ} (A : Set (Space d)) :
    0 ≤ lambdaInner A := by
  exact bot_le

theorem lambdaInner_le_lambdaStar {d : ℕ} (A : Set (Space d)) :
    lambdaInner A ≤ lambdaStar A := by
  refine iSup_le ?_
  intro K
  refine iSup_le ?_
  intro _hK
  refine iSup_le ?_
  intro hKA
  exact lambdaStar_mono hKA

theorem lambdaInner_mono {d : ℕ} {A B : Set (Space d)} (hAB : A ⊆ B) :
    lambdaInner A ≤ lambdaInner B := by
  refine iSup_le ?_
  intro K
  refine iSup_le ?_
  intro hK
  refine iSup_le ?_
  intro hKA
  exact le_iSup_of_le K <|
    le_iSup_of_le hK <|
      le_iSup_of_le (Subset.trans hKA hAB) le_rfl

/-- Compact sets have equal inner and outer measure. -/
theorem lambdaInner_eq_lambdaStar_of_isCompact {d : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) :
    lambdaInner K = lambdaStar K := by
  refine le_antisymm (lambdaInner_le_lambdaStar K) ?_
  exact le_iSup_of_le K <|
    le_iSup_of_le hK <|
      le_iSup_of_le (Subset.rfl : K ⊆ K) le_rfl

/-- A set of outer measure zero has inner measure zero. -/
theorem lambdaInner_eq_zero_of_lambdaStar_eq_zero {d : ℕ} {A : Set (Space d)}
    (hA : lambdaStar A = 0) :
    lambdaInner A = 0 := by
  exact le_antisymm (by simpa [hA] using lambdaInner_le_lambdaStar A) bot_le

/-- Elementary sets are Borel measurable. -/
theorem measurableSet_of_isElementarySet {d : ℕ} {E : Set (Space d)}
    (hE : IsElementarySet E) :
    MeasurableSet E := by
  rcases hE with ⟨n, Q, _hQ, _hdisj, rfl⟩
  refine MeasurableSet.iUnion fun j => ?_
  simpa [Box.Ioc] using
    (MeasurableSet.pi (s := (Set.univ : Set (Fin d))) Set.countable_univ
      (fun i _hi => (measurableSet_Ioc : MeasurableSet (Set.Ioc ((Q j).lower i) ((Q j).upper i)))))

/-- On Borel measurable sets, inner measure agrees with Lebesgue outer measure. -/
theorem lambdaInner_eq_lambdaStar_of_measurableSet {d : ℕ} {A : Set (Space d)}
    (hA : MeasurableSet A) :
    lambdaInner A = lambdaStar A := by
  refine le_antisymm (lambdaInner_le_lambdaStar A) ?_
  rw [lambdaStar]
  rw [hA.measure_eq_iSup_isCompact (μ := (volume : Measure (Space d)))]
  refine iSup_le ?_
  intro K
  refine iSup_le ?_
  intro hKA
  refine iSup_le ?_
  intro hK
  exact le_iSup_of_le K <|
    le_iSup_of_le hK <|
      le_iSup_of_le hKA le_rfl

/-- On open sets, inner measure agrees with Lebesgue outer measure. -/
theorem lambdaInner_eq_lambdaStar_of_isOpen {d : ℕ} {U : Set (Space d)}
    (hU : IsOpen U) :
    lambdaInner U = lambdaStar U :=
  lambdaInner_eq_lambdaStar_of_measurableSet hU.measurableSet

/-! ## 3. Examples -/

/-- Countable subsets of positive-dimensional Euclidean space have inner measure zero. -/
theorem lambdaInner_countable_eq_zero {d : ℕ} [Nonempty (Fin d)]
    {A : Set (Space d)} (hA : A.Countable) :
    lambdaInner A = 0 := by
  exact lambdaInner_eq_zero_of_lambdaStar_eq_zero
    (Chapter03.lambdaStar_countable_eq_zero (d := d) hA)

/-- The rational points in the unit interval, embedded in `ℝ^1`. -/
def rationalUnitInterval : Set (Space 1) :=
  {x | x 0 ∈ Set.range Rat.cast ∧ x 0 ∈ Set.Icc (0 : ℝ) 1}

/-- `ℚ ∩ [0,1]` has inner measure zero. -/
theorem lambdaInner_rationalUnitInterval :
    lambdaInner rationalUnitInterval = 0 := by
  let embed : ℝ → Space 1 := fun r _ => r
  have hRat : (Set.range fun q : ℚ => (q : ℝ)).Countable :=
    Set.countable_range fun q : ℚ => (q : ℝ)
  have hsubset : rationalUnitInterval ⊆ embed '' Set.range (fun q : ℚ => (q : ℝ)) := by
    intro x hx
    refine ⟨x 0, hx.1, ?_⟩
    ext i
    fin_cases i
    rfl
  exact lambdaInner_countable_eq_zero ((hRat.image embed).mono hsubset)

/-! ## 4. Relation with Jordan inner measure -/

/-- Jordan inner measure is bounded by Lebesgue inner measure. -/
theorem jordanInnerMeasure_le_lambdaInner {d : ℕ} (A : Set (Space d)) :
    jordanInnerMeasure A ≤ lambdaInner A := by
  refine iSup_le ?_
  intro E
  refine iSup_le ?_
  intro hE
  refine iSup_le ?_
  intro hEA
  have hEmeas : MeasurableSet E := measurableSet_of_isElementarySet hE
  calc
    elementaryVolume E = lambdaStar E := rfl
    _ = lambdaInner E := (lambdaInner_eq_lambdaStar_of_measurableSet hEmeas).symm
    _ ≤ lambdaInner A := lambdaInner_mono hEA

/-! ## 5. Equivalent descriptions -/

/--
Open-set form of inner measure.  This statement is kept as a bridge to the
interval formula and the later measurable-set criteria.
-/
theorem lambdaInner_eq_open_sub_diff {d : ℕ}
    {A O : Set (Space d)}
    (hAO : A ⊆ O) (hOopen : IsOpen O)
    (_hAfin : lambdaStar A < ⊤) (hOfin : lambdaStar O < ⊤) :
    lambdaInner A = lambdaStar O - lambdaStar (O \ A) := by
  let c : ENNReal := lambdaStar O
  let b : ENNReal := lambdaStar (O \ A)
  have hc_ne_top : c ≠ ⊤ := by
    exact ne_top_of_lt (by simpa [c] using hOfin)
  have hb_le_c : b ≤ c := by
    exact lambdaStar_mono Set.diff_subset
  have hb_ne_top : b ≠ ⊤ := ne_top_of_le_ne_top hc_ne_top hb_le_c
  refine le_antisymm ?upper ?lower
  · change lambdaInner A ≤ c - b
    rw [lambdaInner]
    refine iSup_le ?_
    intro K
    refine iSup_le ?_
    intro hK
    refine iSup_le ?_
    intro hKA
    rw [ENNReal.le_sub_iff_add_le_right hb_ne_top hb_le_c]
    have hKO : K ⊆ O := Subset.trans hKA hAO
    have hsplit : lambdaStar O = lambdaStar (O ∩ K) + lambdaStar (O \ K) :=
      finiteOpen_compact_split hOopen hOfin hK
    have hOintK : O ∩ K = K := Set.inter_eq_self_of_subset_right hKO
    have hb_le_diff : b ≤ lambdaStar (O \ K) := by
      refine lambdaStar_mono ?_
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hKA hxK)⟩
    calc
      lambdaStar K + b ≤ lambdaStar K + lambdaStar (O \ K) :=
        add_le_add le_rfl hb_le_diff
      _ = lambdaStar O := by simpa [hOintK] using hsplit.symm
      _ = c := rfl
  · change c - b ≤ lambdaInner A
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _hInner_lt_top
    let η : ENNReal := (ε : ENNReal) / 2
    have hη_add : η + η = (ε : ENNReal) := by
      dsimp [η]
      exact ENNReal.add_halves _
    have hε' : (ε : ENNReal) ≠ 0 := by
      exact_mod_cast (ne_of_gt hε)
    have hη_ne : η ≠ 0 := by
      dsimp [η]
      exact (ENNReal.div_ne_zero).2 ⟨hε', by norm_num⟩
    rcases Set.exists_isOpen_le_add (O \ A) (volume : Measure (Space d)) hη_ne with
      ⟨U, hOUA, hUopen, hUle⟩
    rcases finiteOpen_innerCompact_exists hOopen hOfin hη_ne with
      ⟨L, hLcompact, hLO, hLapprox⟩
    have hKcompact : IsCompact (L \ U) := hLcompact.diff hUopen
    have hKsubsetA : L \ U ⊆ A := by
      intro x hx
      by_contra hxA
      exact hx.2 (hOUA ⟨hLO hx.1, hxA⟩)
    have hKle : lambdaStar (L \ U) ≤ lambdaInner A := by
      exact le_iSup_of_le (L \ U) <|
        le_iSup_of_le hKcompact <|
          le_iSup_of_le hKsubsetA le_rfl
    have h_inter : L ∩ (L \ U) = L \ U :=
      Set.inter_eq_self_of_subset_right Set.diff_subset
    have h_diff_subset : L \ (L \ U) ⊆ U := by
      intro x hx
      by_contra hxU
      exact hx.2 ⟨hx.1, hxU⟩
    have hsplit : lambdaStar L = lambdaStar (L ∩ (L \ U)) + lambdaStar (L \ (L \ U)) :=
      compact_splits_lambdaStar (C := L \ U) (B := L) hKcompact
    have hUle' : lambdaStar U ≤ b + η := by
      simpa [b, lambdaStar, η] using hUle
    have hc_le : c ≤ (lambdaInner A + (ε : ENNReal)) + b := by
      calc
        c ≤ lambdaStar L + η := by simpa [c] using hLapprox
        _ = (lambdaStar (L \ U) + lambdaStar (L \ (L \ U))) + η := by
          simpa [h_inter] using congrArg (fun x => x + η) hsplit
        _ ≤ (lambdaInner A + lambdaStar U) + η :=
          add_le_add (add_le_add hKle (lambdaStar_mono h_diff_subset)) le_rfl
        _ ≤ (lambdaInner A + (b + η)) + η :=
          add_le_add (add_le_add le_rfl hUle') le_rfl
        _ = (lambdaInner A + (ε : ENNReal)) + b := by
          rw [← hη_add]
          ac_rfl
    exact tsub_le_iff_right.mpr hc_le

/-- Compact-set form of inner measure inside a fixed compact set. -/
theorem lambdaInner_eq_compact_sub_diff {d : ℕ}
    {A C : Set (Space d)} (hAC : A ⊆ C) (hC : IsCompact C) :
    lambdaInner A = lambdaStar C - lambdaStar (C \ A) := by
  let c : ENNReal := lambdaStar C
  let b : ENNReal := lambdaStar (C \ A)
  have hc_ne_top : c ≠ ⊤ := by
    exact ne_top_of_lt
      (by simpa [c, lambdaStar] using hC.measure_lt_top (μ := (volume : Measure (Space d))))
  have hb_le_c : b ≤ c := by
    exact lambdaStar_mono Set.diff_subset
  have hb_ne_top : b ≠ ⊤ := ne_top_of_le_ne_top hc_ne_top hb_le_c
  refine le_antisymm ?upper ?lower
  · change lambdaInner A ≤ c - b
    rw [lambdaInner]
    refine iSup_le ?_
    intro K
    refine iSup_le ?_
    intro hK
    refine iSup_le ?_
    intro hKA
    rw [ENNReal.le_sub_iff_add_le_right hb_ne_top hb_le_c]
    have hKC : K ⊆ C := Subset.trans hKA hAC
    have hsplit : lambdaStar C = lambdaStar (C ∩ K) + lambdaStar (C \ K) :=
      compact_splits_lambdaStar (C := K) (B := C) hK
    have hCintK : C ∩ K = K := Set.inter_eq_self_of_subset_right hKC
    have hb_le_diff : b ≤ lambdaStar (C \ K) := by
      refine lambdaStar_mono ?_
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hKA hxK)⟩
    calc
      lambdaStar K + b ≤ lambdaStar K + lambdaStar (C \ K) :=
        add_le_add le_rfl hb_le_diff
      _ = lambdaStar C := by simpa [hCintK] using hsplit.symm
      _ = c := rfl
  · change c - b ≤ lambdaInner A
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _hInner_lt_top
    have hε' : (ε : ENNReal) ≠ 0 := by
      exact_mod_cast (ne_of_gt hε)
    rcases Set.exists_isOpen_le_add (C \ A) (volume : Measure (Space d)) hε' with
      ⟨U, hCUA, hUopen, hUle⟩
    have hKcompact : IsCompact (C \ U) := hC.diff hUopen
    have hKsubsetA : C \ U ⊆ A := by
      intro x hx
      by_contra hxA
      exact hx.2 (hCUA ⟨hx.1, hxA⟩)
    have hKle : lambdaStar (C \ U) ≤ lambdaInner A := by
      exact le_iSup_of_le (C \ U) <|
        le_iSup_of_le hKcompact <|
          le_iSup_of_le hKsubsetA le_rfl
    have h_inter : C ∩ (C \ U) = C \ U :=
      Set.inter_eq_self_of_subset_right Set.diff_subset
    have h_diff_subset : C \ (C \ U) ⊆ U := by
      intro x hx
      by_contra hxU
      exact hx.2 ⟨hx.1, hxU⟩
    have hsplit : lambdaStar C = lambdaStar (C ∩ (C \ U)) + lambdaStar (C \ (C \ U)) :=
      compact_splits_lambdaStar (C := C \ U) (B := C) hKcompact
    have hUle' : lambdaStar U ≤ b + (ε : ENNReal) := by
      simpa [b, lambdaStar] using hUle
    have hc_le : c ≤ (lambdaInner A + (ε : ENNReal)) + b := by
      calc
        c = lambdaStar (C \ U) + lambdaStar (C \ (C \ U)) := by
          simpa [c, h_inter] using hsplit
        _ ≤ lambdaInner A + lambdaStar U :=
          add_le_add hKle (lambdaStar_mono h_diff_subset)
        _ ≤ lambdaInner A + (b + (ε : ENNReal)) :=
          add_le_add le_rfl hUle'
        _ = (lambdaInner A + (ε : ENNReal)) + b := by ac_rfl
    exact tsub_le_iff_right.mpr hc_le

/--
Interval form of inner measure.  This is the form used in Chapter 05 to test
measurability inside a bounded box.
-/
theorem lambdaInner_eq_boxVolume_sub_lambdaStar_diff {d : ℕ}
    (Q : Box d) {A : Set (Space d)} (hA : A ⊆ Q.Icc) :
    lambdaInner A = Q.volume - lambdaStar (Q.Icc \ A) := by
  have hQcompact : IsCompact Q.Icc := by
    simpa [Box.Icc] using (isCompact_Icc : IsCompact (Set.Icc Q.lower Q.upper))
  calc
    lambdaInner A = lambdaStar Q.Icc - lambdaStar (Q.Icc \ A) :=
      lambdaInner_eq_compact_sub_diff hA hQcompact
    _ = Q.volume - lambdaStar (Q.Icc \ A) := by rw [lambdaStar_boxIcc Q]

/-- Splitting criterion for equality of inner and outer measure inside a box. -/
theorem lambdaInner_eq_lambdaStar_iff_boxVolume_eq {d : ℕ}
    (Q : Box d) {A : Set (Space d)} (hA : A ⊆ Q.Icc) :
    lambdaInner A = lambdaStar A ↔
      Q.volume = lambdaStar A + lambdaStar (Q.Icc \ A) := by
  have hformula := lambdaInner_eq_boxVolume_sub_lambdaStar_diff Q hA
  have hb_le_c : lambdaStar (Q.Icc \ A) ≤ Q.volume := by
    calc
      lambdaStar (Q.Icc \ A) ≤ lambdaStar Q.Icc := lambdaStar_mono Set.diff_subset
      _ = Q.volume := lambdaStar_boxIcc Q
  have hc_ne_top : Q.volume ≠ ⊤ := by
    rw [Box.volume]
    exact ENNReal.prod_ne_top (s := Finset.univ)
      (f := fun i : Fin d => ENNReal.ofReal (Q.upper i - Q.lower i))
      (by intro _i _hi; exact ENNReal.ofReal_ne_top)
  have hb_ne_top : lambdaStar (Q.Icc \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top hc_ne_top hb_le_c
  rw [hformula]
  constructor
  · intro h
    calc
      Q.volume = (Q.volume - lambdaStar (Q.Icc \ A)) + lambdaStar (Q.Icc \ A) :=
        (tsub_add_cancel_of_le hb_le_c).symm
      _ = lambdaStar A + lambdaStar (Q.Icc \ A) := by rw [h]
  · intro h
    exact ENNReal.sub_eq_of_eq_add hb_ne_top h

/-! ## 6. Interpretation -/

/--
Lebesgue-style measurability from Chapter 04: outer measure agrees with inner
measure.  Chapter 05 will compare this with the usual measurable sets.
-/
def LebesgueMeasurableByInner {d : ℕ} (A : Set (Space d)) : Prop :=
  lambdaInner A = lambdaStar A

theorem lebesgueMeasurableByInner_iff {d : ℕ} {A : Set (Space d)} :
    LebesgueMeasurableByInner A ↔ lambdaInner A = lambdaStar A := by
  rfl

end Chapter04
end NoteKsk
