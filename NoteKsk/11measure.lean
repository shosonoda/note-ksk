/-
  Lebesgue 積分論ノート（導入）
  1) 有限加法族（algebra of sets）
  2) 完全加法族（σ-代数 = measurable space）
  3) 外測度
  4) 測度
-/

import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.MeasureSpace

open Finset Set MeasurableSpace  --- Finset.Insert
open scoped BigOperators

namespace LebesgueNotes

universe u v
variable {α : Type u} {ι : Type v}

--------------------------------------------------------------------------------
-- 1. 有限加法族（algebra of sets）
--------------------------------------------------------------------------------

/-- 有限加法族（Tao: algebra of sets）。
`C : Set (Set α)` が
- `∅ ∈ C`
- `s ∈ C → sᶜ ∈ C`
- `s,t ∈ C → s ∪ t ∈ C`
を満たすこと。Mathlib では `MeasureTheory.IsSetAlgebra C`。 -/
-- abbrev FiniteAdditiveFamily (C : Set (Set α)) : Prop :=
--   MeasureTheory.IsSetAlgebra C
structure FiniteAdditiveFamily (𝒜 : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ 𝒜
  compl_mem : ∀ ⦃s⦄, s ∈ 𝒜 → sᶜ ∈ 𝒜
  union_mem : ∀ ⦃s t⦄, s ∈ 𝒜 → t ∈ 𝒜 → s ∪ t ∈ 𝒜

namespace FiniteAdditiveFamily

variable {s t : Set α} {C : Set (Set α)} --- {hC : FiniteAdditiveFamily C}

lemma empty_mem' (hC : FiniteAdditiveFamily C) : (∅ : Set α) ∈ C :=
  hC.empty_mem

lemma compl_mem' (hC : FiniteAdditiveFamily C) (hs : s ∈ C) : sᶜ ∈ C :=
  hC.compl_mem hs

lemma union_mem' (hC : FiniteAdditiveFamily C) (hs : s ∈ C) (ht : t ∈ C) : s ∪ t ∈ C :=
  hC.union_mem hs ht

/-- `univ` も入る（`∅` と補集合から）。 -/
lemma univ_mem (hC : FiniteAdditiveFamily C) : (Set.univ : Set α) ∈ C :=
  compl_empty ▸ hC.compl_mem hC.empty_mem
  -- MeasureTheory.IsSetAlgebra.univ_mem (h := hC)

/-- 交わりも入る（De Morgan で補集合と和から）。 -/
lemma inter_mem (hC : FiniteAdditiveFamily C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C :=
  inter_eq_compl_compl_union_compl .. ▸
  hC.compl_mem ( hC.union_mem ( hC.compl_mem hs ) (hC.compl_mem ht) )
  -- MeasureTheory.IsSetAlgebra.inter_mem (h := hC) hs ht

/-- 差集合も入る（`s \ t = s ∩ tᶜ`）。 -/
lemma diff_mem (hC : FiniteAdditiveFamily C) (hs : s ∈ C) (ht : t ∈ C) : s \ t ∈ C :=
  hC.inter_mem hs (hC.compl_mem ht)
  -- MeasureTheory.IsSetAlgebra.diff_mem (h := hC) hs ht

/-- 有限和（`Finset` 添字の二重 `iUnion`）で閉じる（帰納法）。 -/
lemma biUnion_mem (hC : FiniteAdditiveFamily C) (s : ι → Set α) (S : Finset ι)
    (hs : ∀ i ∈ S, s i ∈ C) :
    (⋃ i ∈ S, s i) ∈ C := by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS ↦ hs n (mem_insert_of_mem hnS))
  -- MeasureTheory.IsSetAlgebra.biUnion_mem (h := hC) S hs

/-- 有限交わり（`Finset` 添字の二重 `iInter`）で閉じる。-/
lemma biInter_mem (hC : FiniteAdditiveFamily C) (s : ι → Set α) (S : Finset ι) (hS : S.Nonempty)
    (hs : ∀ i ∈ S, s i ∈ C) :
    (⋂ i ∈ S, s i) ∈ C := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS ↦ hs.2 n hnS)
  -- MeasureTheory.IsSetAlgebra.biInter_mem (h := hC) S hs

end FiniteAdditiveFamily

/-- 与えられた族 `C` が生成する最小の有限加法族。Mathlib: `generateSetAlgebra`. -/
abbrev finGen (C : Set (Set α)) : Set (Set α) :=
  MeasureTheory.generateSetAlgebra C

/-- `finGen C` は有限加法族。-/
lemma FiniteAdditiveFamily_finGen (C : Set (Set α)) :
    FiniteAdditiveFamily (α := α) (finGen (α := α) C) :=
  (MeasureTheory.isSetAlgebra_generateSetAlgebra (s := C))

/-- `C ⊆ finGen C`（生成族は含まれる）。-/
lemma subset_finGen (C : Set (Set α)) :
    C ⊆ finGen (α := α) C :=
  (MeasureTheory.self_subset_generateSetAlgebra (s := C))

/-- `σ`-代数生成は，先に有限加法閉包しても同じ。-/
@[simp] lemma generateFrom_finGen_eq (C : Set (Set α)) :
    MeasurableSpace.generateFrom (finGen (α := α) C)
      = MeasurableSpace.generateFrom C :=
  (MeasureTheory.generateFrom_generateSetAlgebra_eq (s := C))

--------------------------------------------------------------------------------
-- 2. 完全加法族（σ-代数）
--------------------------------------------------------------------------------

/-- 完全加法族（σ-代数）は `MeasurableSpace α` として扱う。-/
abbrev CompleteAdditiveFamily (α : Type u) : Type u :=
  MeasurableSpace α

section SigmaAlgebra

variable [m : MeasurableSpace α]

/- `MeasurableSet s` が「`s` が σ-代数に属する」こと。-/

lemma measurable_empty : MeasurableSet (∅ : Set α) :=
  by simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set α))

lemma measurable_compl {s : Set α} (hs : MeasurableSet s) : MeasurableSet sᶜ :=
  hs.compl

lemma measurable_union (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∪ t) :=
  hs.union ht

lemma measurable_inter (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ t) :=
  hs.inter ht

lemma measurable_diff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s \ t) :=
  hs.diff ht

/-- 可算和で閉じる（`Countable ι` を仮定）。 -/
lemma measurable_iUnion {ι : Sort v} [Countable ι] (f : ι → Set α)
    (hf : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋃ i, f i) :=
  MeasurableSet.iUnion hf

/-- 可算交わりで閉じる（`Countable ι` を仮定）。 -/
lemma measurable_iInter {ι : Sort v} [Countable ι] (f : ι → Set α)
    (hf : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋂ i, f i) :=
  MeasurableSet.iInter hf

/-- （確認）可測集合全体 `{s | MeasurableSet s}` は有限加法族。 -/
lemma measurableSets_FiniteAdditiveFamily :
    FiniteAdditiveFamily (α := α) {s : Set α | MeasurableSet s} := by
  refine ⟨?_, ?_, ?_⟩
  · -- empty
    simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set α) )
  · -- compl
    intro s hs
    simpa using hs.compl
  · -- union
    intro s t hs ht
    simpa using hs.union ht

end SigmaAlgebra

--------------------------------------------------------------------------------
-- 3. 外測度（OuterMeasure）
--------------------------------------------------------------------------------

/-- 外測度（Mathlib: `MeasureTheory.OuterMeasure α`）。 -/
abbrev OuterMeasure (α : Type u) : Type u :=
  MeasureTheory.OuterMeasure α

namespace OuterMeasure

variable (μ : MeasureTheory.OuterMeasure α)

/-- 外測度の公理 (1): `μ ∅ = 0`。 -/
lemma empty : μ (∅ : Set α) = 0 :=
  by simpa using (MeasureTheory.measure_empty (μ := μ))

/-- 外測度の公理 (2): 単調性。 -/
lemma mono (h : s ⊆ t) : μ s ≤ μ t :=
  MeasureTheory.measure_mono (μ := μ) h

/-- 外測度の公理 (3): 可算劣加法性（一般形は `measure_iUnion_le` として使える）。 -/
lemma iUnion_le [Countable ι] (s : ι → Set α) :
    μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  MeasureTheory.measure_iUnion_le (μ := μ) s

/-- 特に二つの和について劣加法性。 -/
lemma union_le (s t : Set α) : μ (s ∪ t) ≤ μ s + μ t :=
  MeasureTheory.measure_union_le (μ := μ) s t

end OuterMeasure

--------------------------------------------------------------------------------
-- 4. 測度（Measure）
--------------------------------------------------------------------------------

section Measure

variable [MeasurableSpace α]

/-- 測度（Mathlib: `MeasureTheory.Measure α`）。-/
abbrev Measure (α : Type u) : Type u :=
  MeasureTheory.Measure α

namespace Measure

variable (μ : MeasureTheory.Measure α)

lemma empty : μ (∅ : Set α) = 0 :=
  by simpa using (MeasureTheory.measure_empty (μ := μ))

lemma mono (h : s ⊆ t) : μ s ≤ μ t :=
  MeasureTheory.measure_mono (μ := μ) h

/-- 測度は（外測度として）可算劣加法的。 -/
lemma iUnion_le [Countable ι] (s : ι → Set α) :
    μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  MeasureTheory.measure_iUnion_le (μ := μ) s

/-- 測度の（定義に含まれる）可測集合上での可算加法性：
可測で互いに素な列 `f : ℕ → Set α` に対し `μ (⋃ i, f i) = ∑' i, μ (f i)`。 -/
theorem iUnion_of_disjoint (f : ℕ → Set α)
    (hf : ∀ i, MeasurableSet (f i))
    (hdis : Pairwise (Disjoint f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) := by
  simpa using μ.m_iUnion (f := f) hf hdis

/-- 有限加法性の典型例：互いに素な和集合の測度。 -/
theorem union (s₁ s₂ : Set α) (hd : Disjoint s₁ s₂) (h₂ : MeasurableSet s₂) :
    μ (s₁ ∪ s₂) = μ s₁ + μ s₂ := by
  simpa using (MeasureTheory.measure_union (μ := μ) (s₁ := s₁) (s₂ := s₂) hd h₂)

/-- 分割公式：`μ (s ∩ t) + μ (s \\ t) = μ s`（`t` 可測）。 -/
theorem inter_add_diff (s t : Set α) (ht : MeasurableSet t) :
    μ (s ∩ t) + μ (s \ t) = μ s := by
  simpa using (MeasureTheory.measure_inter_add_diff (μ := μ) (s := s) (t := t) ht)

end Measure

end Measure

end LebesgueNotes
