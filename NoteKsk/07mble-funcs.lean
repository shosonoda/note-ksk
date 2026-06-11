/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«06caratheodory»

/-!
# Chapter 07: Measurable functions

This file follows `blueprint/src/chapters/07mble-funcs.tex`.

Mathlib already provides the central notions:

* measurable spaces are `MeasurableSpace`s;
* measurable maps and measurable functions are `Measurable`;
* the Borel structure on `EReal` is the standard order-topology Borel space;
* almost-everywhere statements are expressed by the filter `Measure.ae`.

The lecture-note definitions are therefore mostly recorded as aliases in
`Defs.lean`, and this chapter supplies the corresponding theorem names.

Two small changes from the notes are intentional and documented near the
statements:

* for the main measurable-function criterion, the fully proved Lean statement
  uses all `EReal` thresholds.  The lecture version using only real thresholds
  is also recorded as a named bridge theorem;
* real reciprocal is available in mathlib as the total function with `0⁻¹ = 0`.
  We still record the note's nonzero-domain version.
-/

noncomputable section

open scoped BigOperators Topology ENNReal
open Set MeasureTheory Filter

namespace NoteKsk
open Chapter05 Chapter06

namespace Chapter07

/-! ## 2. Measurable maps -/

section MeasurableMaps

variable {α β γ ι : Type*}

theorem measurableMap_iff_preimage [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} :
    MeasurableMap f ↔ ∀ ⦃B : Set β⦄, MeasurableSet B → MeasurableSet (f ⁻¹' B) := by
  constructor
  · intro hf B hB
    exact hf hB
  · intro h B hB
    exact h hB

theorem preimage_compl (f : α → β) (B : Set β) :
    f ⁻¹' Bᶜ = (f ⁻¹' B)ᶜ := by
  ext x
  simp

theorem preimage_iUnion (f : α → β) (B : ι → Set β) :
    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

theorem preimage_iInter (f : α → β) (B : ι → Set β) :
    f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

/-- The inverse-image σ-algebra induced by a map. -/
abbrev inducedMeasurableSpace (f : α → β) [MeasurableSpace β] : MeasurableSpace α :=
  MeasurableSpace.comap f inferInstance

theorem inducedMeasurableSpace_measurable (f : α → β) [MeasurableSpace β] :
    @Measurable α β (inducedMeasurableSpace f) inferInstance f := by
  intro B hB
  exact ⟨B, hB, rfl⟩

theorem comap_generatedSigmaAlgebra (f : α → β) (C : Set (Set β)) :
    MeasurableSpace.comap f (generatedSigmaAlgebra C) =
      generatedSigmaAlgebra (preimageFamily f C) := by
  simpa [generatedSigmaAlgebra, preimageFamily] using
    (MeasurableSpace.comap_generateFrom (f := f) (s := C))

theorem measurable_to_generatedSigmaAlgebra (f : α → β) (C : Set (Set β)) :
    @Measurable α β (generatedSigmaAlgebra (preimageFamily f C))
      (generatedSigmaAlgebra C) f := by
  rw [measurable_iff_comap_le]
  simpa [generatedSigmaAlgebra, preimageFamily] using
    (le_of_eq (MeasurableSpace.comap_generateFrom (f := f) (s := C)))

theorem measurable_comp [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → β} {g : β → γ}
    (hg : MeasurableMap g) (hf : MeasurableMap f) :
    MeasurableMap (g ∘ f) := by
  exact hg.comp hf

end MeasurableMaps

/-! ## 3. Extended-real-valued measurable functions -/

section ERealFunctions

variable {α : Type*} [MeasurableSpace α]

/--
Mathlib proves `borel_eq_generateFrom_Iic` for all endpoints in an ordered
Borel space.  The lecture notes use only finite real endpoints in `EReal`; this
bridge theorem records that form.
-/
theorem borel_eReal_eq_generate_Iic_real :
    (borel EReal) =
      generatedSigmaAlgebra (Set.range fun a : ℝ => Set.Iic (a : EReal)) := by
  let C : Set (Set EReal) := Set.range fun a : ℝ => Set.Iic (a : EReal)
  rw [borel_eq_generateFrom_Iic EReal]
  change MeasurableSpace.generateFrom (Set.range (Set.Iic : EReal → Set EReal)) =
    MeasurableSpace.generateFrom C
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨a, rfl⟩
    induction a with
    | bot =>
        have hEq :
            Set.Iic (⊥ : EReal) = (⋂ n : ℕ, Set.Iic ((-(n : ℝ) : ℝ) : EReal)) := by
          ext x
          constructor
          · intro hx
            exact Set.mem_iInter.mpr fun n =>
              le_trans hx (bot_le : (⊥ : EReal) ≤ ((-(n : ℝ) : ℝ) : EReal))
          · intro hx
            induction x with
            | bot =>
                change (⊥ : EReal) ≤ ⊥
                exact le_rfl
            | top =>
                have h0 := Set.mem_iInter.mp hx 0
                simp at h0
            | coe r =>
                exfalso
                have hxall : ∀ n : ℕ, r ≤ -(n : ℝ) := by
                  intro n
                  have hn := Set.mem_iInter.mp hx n
                  exact EReal.coe_le_coe_iff.mp hn
                obtain ⟨n, hn⟩ := exists_nat_gt (-r)
                have hnr : r > -(n : ℝ) := by linarith
                exact (not_lt_of_ge (hxall n)) hnr
        rw [hEq]
        refine MeasurableSet.iInter fun n => ?_
        exact MeasurableSpace.measurableSet_generateFrom
          (s := C) ⟨(-(n : ℝ) : ℝ), rfl⟩
    | coe r =>
        exact MeasurableSpace.measurableSet_generateFrom (s := C) ⟨r, rfl⟩
    | top =>
        simp
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨a, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨(a : EReal), rfl⟩

theorem measurable_ereal_criterion_all_thresholds (f : α → EReal) :
    Measurable f ↔
      (∀ a : EReal, MeasurableSet {x | f x > a}) ∧
      (∀ a : EReal, MeasurableSet {x | f x ≥ a}) ∧
      (∀ a : EReal, MeasurableSet {x | f x < a}) ∧
      (∀ a : EReal, MeasurableSet {x | f x ≤ a}) := by
  constructor
  · intro hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      exact measurableSet_lt measurable_const hf
    · intro a
      exact measurableSet_le measurable_const hf
    · intro a
      exact measurableSet_lt hf measurable_const
    · intro a
      exact measurableSet_le hf measurable_const
  · rintro ⟨hgt, _hge, _hlt, _hle⟩
    exact measurable_of_Ioi (f := f) (by
      simpa [Set.preimage, Set.mem_Ioi] using hgt)

/--
Lecture-note criterion `thm:lebesgue-measurable-function-criterion`.

The blueprint states the criterion with thresholds `a : ℝ`.  The theorem above
is the mathlib-native all-`EReal` version; this statement keeps the exact
lecture form as a bridge for later chapters.
-/
theorem measurable_ereal_real_level_criterion (f : α → EReal) :
    Measurable f ↔
      (∀ a : ℝ, MeasurableSet {x | f x > (a : EReal)}) ∧
      (∀ a : ℝ, MeasurableSet {x | f x ≥ (a : EReal)}) ∧
      (∀ a : ℝ, MeasurableSet {x | f x < (a : EReal)}) ∧
      (∀ a : ℝ, MeasurableSet {x | f x ≤ (a : EReal)}) := by
  constructor
  · intro hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      exact measurableSet_lt measurable_const hf
    · intro a
      exact measurableSet_le measurable_const hf
    · intro a
      exact measurableSet_lt hf measurable_const
    · intro a
      exact measurableSet_le hf measurable_const
  · rintro ⟨_hgt, _hge, _hlt, hle⟩
    convert! measurable_generateFrom (α := α)
      (s := Set.range fun a : ℝ => Set.Iic (a : EReal)) (f := f) ?_
    · exact borel_eReal_eq_generate_Iic_real
    · rintro _ ⟨a, rfl⟩
      exact hle a

theorem measurableFunction_const (c : EReal) :
    Measurable (fun _ : α => c) := by
  exact measurable_const

end ERealFunctions

/-! ## 4. Basic examples -/

section Examples

variable {α β : Type*}

theorem continuous_borelMeasurable [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : α → β} (hf : Continuous f) :
    Measurable f := by
  exact hf.measurable

theorem indicator_measurable [MeasurableSpace α] {A : Set α}
    (hA : MeasurableSet A) :
    Measurable (A.indicator fun _ : α => (1 : ℝ)) := by
  exact measurable_const.indicator hA

/-- The rational points in the real line. -/
def rationalSet : Set ℝ :=
  Set.range fun q : ℚ => (q : ℝ)

/-- The rational points in `[0, 1]`. -/
def rationalUnitInterval : Set ℝ :=
  rationalSet ∩ Set.Icc (0 : ℝ) 1

/-- The Dirichlet indicator from the motivation section, as a function on `ℝ`. -/
def dirichletFunction01 : ℝ → ℝ :=
  rationalUnitInterval.indicator fun _ => (1 : ℝ)

theorem rationalSet_countable :
    rationalSet.Countable := by
  simpa [rationalSet] using (Set.countable_range fun q : ℚ => (q : ℝ))

theorem rationalUnitInterval_measurableSet :
    MeasurableSet rationalUnitInterval := by
  exact rationalSet_countable.measurableSet.inter measurableSet_Icc

theorem dirichletFunction01_measurable :
    Measurable dirichletFunction01 := by
  exact measurable_const.indicator rationalUnitInterval_measurableSet

end Examples

/-! ## 5. Vector-valued maps and composition -/

section VectorAndAlgebra

variable {α : Type*} [MeasurableSpace α]

theorem measurable_vector_map {n : ℕ} (f : Fin n → α → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    Measurable fun x : α => fun i => f i x := by
  exact measurable_pi_iff.mpr hf

theorem measurable_continuous_comp {n : ℕ}
    {F : α → Fin n → ℝ} {φ : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hφ : Continuous φ) :
    Measurable (φ ∘ F) := by
  exact hφ.measurable.comp hF

theorem measurable_const_mul {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    Measurable fun x => c * f x := by
  exact hf.const_mul c

theorem measurable_add {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x + g x := by
  exact hf.add hg

theorem measurable_mul {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x := by
  exact hf.mul hg

theorem measurable_max {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => max (f x) (g x) := by
  exact hf.max hg

theorem measurable_min {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => min (f x) (g x) := by
  exact hf.min hg

theorem measurable_abs_rpow {f : α → ℝ} (hf : Measurable f)
    (p : ℝ) (_hp : 0 < p) :
    Measurable fun x => |f x| ^ p := by
  exact hf.abs.pow_const p

theorem measurable_continuous_real_comp {f : α → ℝ} {φ : ℝ → ℝ}
    (hf : Measurable f) (hφ : Continuous φ) :
    Measurable (φ ∘ f) := by
  exact hφ.measurable.comp hf

theorem measurable_nonzero_set {f : α → ℝ} (hf : Measurable f) :
    MeasurableSet {x | f x ≠ 0} := by
  have hEq : MeasurableSet {x | f x = 0} :=
    measurableSet_eq_fun hf measurable_const
  exact hEq.compl

theorem measurable_reciprocal_on_nonzero {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x : {x : α // f x ≠ 0} => (f x)⁻¹ := by
  exact hf.inv.comp measurable_subtype_coe

/--
Mathlib also gives the total reciprocal on `ℝ`, with the convention `0⁻¹ = 0`.
This is stronger as a measurability statement than the restricted-domain form
used in the lecture notes.
-/
theorem measurable_reciprocal_global {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => (f x)⁻¹ := by
  exact hf.inv

end VectorAndAlgebra

/-! ## 6. Sets and functions built from inequalities and limits -/

section Limits

variable {α : Type*} [MeasurableSpace α]

theorem measurableSet_gt_of_measurable {f g : α → EReal}
    (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x > g x} := by
  exact measurableSet_lt hg hf

theorem measurableSet_ge_of_measurable {f g : α → EReal}
    (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x ≥ g x} := by
  exact measurableSet_le hg hf

theorem measurableSet_eq_of_measurable {f g : α → EReal}
    (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x = g x} := by
  exact measurableSet_eq_fun hf hg

theorem measurable_pointwiseSup (f : ℕ → α → EReal)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (pointwiseSup f) := by
  simpa [pointwiseSup] using (Measurable.iSup (f := f) hf)

theorem measurable_pointwiseInf (f : ℕ → α → EReal)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (pointwiseInf f) := by
  simpa [pointwiseInf] using (Measurable.iInf (f := f) hf)

theorem measurable_pointwiseLimsup (f : ℕ → α → EReal)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (pointwiseLimsup f) := by
  simpa [pointwiseLimsup] using (Measurable.limsup (f := f) hf)

theorem measurable_pointwiseLiminf (f : ℕ → α → EReal)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (pointwiseLiminf f) := by
  simpa [pointwiseLiminf] using (Measurable.liminf (f := f) hf)

theorem measurable_of_eq_pointwiseLimsup {f : ℕ → α → EReal} {g : α → EReal}
    (hf : ∀ n, Measurable (f n)) (hg : g = pointwiseLimsup f) :
    Measurable g := by
  rw [hg]
  exact measurable_pointwiseLimsup f hf

/--
Pointwise convergence version of `prop:measurable-limsup-liminf`.

The proof can be filled by identifying the pointwise limit with both limsup and
liminf.  It is kept as a named statement because later integration chapters
usually refer to this form directly.
-/
theorem measurable_of_pointwise_tendsto {f : ℕ → α → EReal} {g : α → EReal}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (𝓝 (g x))) :
    Measurable g := by
  exact measurable_of_tendsto_metrizable hf (by simpa [tendsto_pi_nhds] using hlim)

end Limits

/-! ## 7. Almost everywhere and a.e. convergence -/

section AlmostEverywhere

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem aeEqualOn_equivalence (μ : Measure α) (E : Set α) :
    Equivalence (AEEqualOn (α := α) (β := β) μ E) := by
  constructor
  · intro f
    exact EventuallyEq.rfl
  · intro f g hfg
    exact hfg.symm
  · intro f g h hfg hgh
    exact hfg.trans hgh

theorem measurable_of_ae_eq_complete {μ : Measure α} [μ.IsComplete]
    {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) :
    Measurable g := by
  exact Measurable.congr_ae hf hfg

end AlmostEverywhere

section AEConvergence

variable {α : Type*} [MeasurableSpace α]

theorem measurable_of_ae_tendsto_real {μ : Measure α} [μ.IsComplete]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (𝓝 (g x))) :
    Measurable g := by
  exact measurable_of_tendsto_metrizable_ae hf hlim

theorem measurable_of_ae_tendsto_ereal {μ : Measure α} [μ.IsComplete]
    {f : ℕ → α → EReal} {g : α → EReal}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (𝓝 (g x))) :
    Measurable g := by
  exact measurable_of_tendsto_metrizable_ae hf hlim

end AEConvergence

end Chapter07
end NoteKsk
