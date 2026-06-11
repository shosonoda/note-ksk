/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 09: Properties of the Lebesgue integral

This file follows `blueprint/src/chapters/09lintegral-prop.tex`.

The lecture notes state the basic calculus rules for the Lebesgue integral:
positive and negative parts, null-set invariance, a.e. invariance, monotonicity,
linearity, finite sums, and Chebyshev's inequality.

As in Chapter 08, signed real-valued integrals are formalized using mathlib's
Bochner integral.  Chebyshev's inequality is stated first in mathlib's native
`ENNReal` form for measures and lower Lebesgue integrals; the real-valued
version below rewrites the threshold set `{|f| ≥ a}` into that form.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open Set MeasureTheory Filter

namespace NoteKsk

namespace Chapter09

/-! ## 1. Positive and negative parts -/

section PositiveNegativeParts

variable {α : Type*}

theorem realPositivePart_nonneg (f : α → ℝ) (x : α) :
    0 ≤ realPositivePart f x := by
  exact le_max_right (f x) 0

theorem realNegativePart_nonneg (f : α → ℝ) (x : α) :
    0 ≤ realNegativePart f x := by
  exact le_max_right (-f x) 0

theorem realPositivePart_sub_realNegativePart (f : α → ℝ) (x : α) :
    realPositivePart f x - realNegativePart f x = f x := by
  by_cases h : 0 ≤ f x
  · have hneg : -f x ≤ 0 := neg_nonpos.mpr h
    simp [realPositivePart, realNegativePart, max_eq_left h, max_eq_right hneg]
  · have hlt : f x < 0 := lt_of_not_ge h
    have hf_le : f x ≤ 0 := hlt.le
    have hneg_nonneg : 0 ≤ -f x := neg_nonneg.mpr hf_le
    simp [realPositivePart, realNegativePart, max_eq_right hf_le, max_eq_left hneg_nonneg]

theorem realPositivePart_add_realNegativePart (f : α → ℝ) (x : α) :
    realPositivePart f x + realNegativePart f x = |f x| := by
  by_cases h : 0 ≤ f x
  · have hneg : -f x ≤ 0 := neg_nonpos.mpr h
    simp [realPositivePart, realNegativePart, max_eq_left h, max_eq_right hneg,
      abs_of_nonneg h]
  · have hlt : f x < 0 := lt_of_not_ge h
    have hf_le : f x ≤ 0 := hlt.le
    have hneg_nonneg : 0 ≤ -f x := neg_nonneg.mpr hf_le
    simp [realPositivePart, realNegativePart, max_eq_right hf_le, max_eq_left hneg_nonneg,
      abs_of_neg hlt]

theorem realPositivePart_mul_realNegativePart (f : α → ℝ) (x : α) :
    realPositivePart f x * realNegativePart f x = 0 := by
  by_cases h : 0 ≤ f x
  · have hneg : -f x ≤ 0 := neg_nonpos.mpr h
    simp [realPositivePart, realNegativePart, max_eq_left h, max_eq_right hneg]
  · have hlt : f x < 0 := lt_of_not_ge h
    have hf_le : f x ≤ 0 := hlt.le
    have hneg_nonneg : 0 ≤ -f x := neg_nonneg.mpr hf_le
    simp [realPositivePart, realNegativePart, max_eq_right hf_le, max_eq_left hneg_nonneg]

end PositiveNegativeParts

/-! ## 2. Integrability as a difference of nonnegative functions -/

section DifferenceRepresentation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem realPositivePart_integrable {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (realPositivePart f) μ := by
  simpa [realPositivePart] using hf.pos_part

theorem realNegativePart_integrable {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (realNegativePart f) μ := by
  simpa [realNegativePart] using hf.neg_part

/--
The lecture statement uses pointwise nonnegative measurable functions and
pointwise equality `f = u - v`.  This formal version uses a.e. nonnegativity
and a.e. equality, which is the mathlib-native formulation for Bochner
integrals and is equivalent for integration purposes.
-/
theorem integrable_iff_exists_integrable_sub_nonneg {f : α → ℝ} :
    Integrable f μ ↔
      ∃ u v : α → ℝ,
        Integrable u μ ∧ Integrable v μ ∧
        (0 ≤ᶠ[ae μ] u) ∧ (0 ≤ᶠ[ae μ] v) ∧
        f =ᵐ[μ] fun x => u x - v x := by
  constructor
  · intro hf
    refine ⟨realPositivePart f, realNegativePart f,
      realPositivePart_integrable (μ := μ) hf,
      realNegativePart_integrable (μ := μ) hf, ?_, ?_, ?_⟩
    · filter_upwards [] with x
      exact realPositivePart_nonneg f x
    · filter_upwards [] with x
      exact realNegativePart_nonneg f x
    · filter_upwards [] with x
      exact (realPositivePart_sub_realNegativePart f x).symm
  · rintro ⟨u, v, hu, hv, _hu_nonneg, _hv_nonneg, hfg⟩
    exact (hu.sub hv).congr hfg.symm

theorem integral_eq_sub_of_ae_eq_sub {f u v : α → ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ)
    (hfg : f =ᵐ[μ] fun x => u x - v x) :
    (∫ x, f x ∂μ) = (∫ x, u x ∂μ) - ∫ x, v x ∂μ := by
  calc
    (∫ x, f x ∂μ) = ∫ x, u x - v x ∂μ :=
      MeasureTheory.integral_congr_ae hfg
    _ = (∫ x, u x ∂μ) - ∫ x, v x ∂μ := by
      simpa using MeasureTheory.integral_sub (μ := μ) hu hv

theorem integral_eq_realPositivePart_sub_realNegativePart {f : α → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) =
      (∫ x, realPositivePart f x ∂μ) - ∫ x, realNegativePart f x ∂μ := by
  exact integral_eq_sub_of_ae_eq_sub
    (μ := μ)
    (realPositivePart_integrable (μ := μ) hf)
    (realNegativePart_integrable (μ := μ) hf)
    (by
      filter_upwards [] with x
      exact (realPositivePart_sub_realNegativePart f x).symm)

end DifferenceRepresentation

/-! ## 3. Set properties and almost-everywhere invariance -/

section SetProperties

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_eq_zero_of_measure_univ_zero {f : α → ℝ}
    (hμ : μ Set.univ = 0) :
    (∫ x, f x ∂μ) = 0 := by
  simpa using MeasureTheory.setIntegral_measure_zero (μ := μ) (s := Set.univ) f hμ

theorem setIntegral_eq_zero_of_measure_zero {N : Set α} (hN : μ N = 0)
    (f : α → ℝ) :
    (∫ x in N, f x ∂μ) = 0 := by
  exact MeasureTheory.setIntegral_measure_zero f hN

theorem setIntegral_union_of_disjoint {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E}
    {A B : Set α} (hAB : Disjoint A B) (hB : MeasurableSet B)
    (hfA : IntegrableOn f A μ) (hfB : IntegrableOn f B μ) :
    (∫ x in A ∪ B, f x ∂μ) =
      (∫ x in A, f x ∂μ) + ∫ x in B, f x ∂μ := by
  exact MeasureTheory.setIntegral_union hAB hB hfA hfB

theorem setIntegral_union_of_disjoint_of_integrable {f : α → ℝ}
    (hf : Integrable f μ) {A B : Set α}
    (hAB : Disjoint A B) (hB : MeasurableSet B) :
    (∫ x in A ∪ B, f x ∂μ) =
      (∫ x in A, f x ∂μ) + ∫ x in B, f x ∂μ := by
  exact setIntegral_union_of_disjoint (μ := μ) hAB hB hf.integrableOn hf.integrableOn

theorem integral_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : α → E} (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  exact MeasureTheory.integral_congr_ae hfg

theorem integrable_congr_ae {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f g : α → E} (hf : Integrable f μ) (hfg : f =ᵐ[μ] g) :
    Integrable g μ := by
  exact hf.congr hfg

theorem integral_aestrongly_congr {f g : α → ℝ}
    (hf : Integrable f μ) (hfg : f =ᵐ[μ] g) :
    Integrable g μ ∧ (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  exact ⟨hf.congr hfg, MeasureTheory.integral_congr_ae hfg⟩

end SetProperties

/-! ## 4. Order and size estimates -/

section OrderAndSize

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_mono_ae_real {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f ≤ᶠ[ae μ] g) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  exact MeasureTheory.integral_mono_ae hf hg hfg

theorem integral_mono_real {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f ≤ g) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  exact MeasureTheory.integral_mono hf hg hfg

theorem integral_bounds_of_ae_const_le [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) {a b : ℝ}
    (ha : (fun _ : α => a) ≤ᶠ[ae μ] f)
    (hb : f ≤ᶠ[ae μ] fun _ : α => b) :
    a * μ.real Set.univ ≤ (∫ x, f x ∂μ) ∧
      (∫ x, f x ∂μ) ≤ b * μ.real Set.univ := by
  constructor
  · have hle := MeasureTheory.integral_mono_ae (μ := μ)
      (MeasureTheory.integrable_const (α := α) (μ := μ) a) hf ha
    simpa [MeasureTheory.integral_const, mul_comm] using hle
  · have hle := MeasureTheory.integral_mono_ae (μ := μ) hf
      (MeasureTheory.integrable_const (α := α) (μ := μ) b) hb
    simpa [MeasureTheory.integral_const, mul_comm] using hle

theorem abs_integral_le_integral_abs (f : α → ℝ) :
    |(∫ x, f x ∂μ)| ≤ ∫ x, |f x| ∂μ := by
  simpa [Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_integral_norm (μ := μ) f)

theorem norm_integral_le_integral_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : α → E) :
    ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  exact MeasureTheory.norm_integral_le_integral_norm (μ := μ) f

theorem integral_abs_eq_zero_iff_ae_eq_zero {f : α → ℝ}
    (hf : Integrable f μ) :
    (∫ x, |f x| ∂μ) = 0 ↔ f =ᵐ[μ] 0 := by
  have hnonneg : 0 ≤ᶠ[ae μ] fun x => |f x| := by
    filter_upwards [] with x
    exact abs_nonneg (f x)
  have hiff := MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (μ := μ) hnonneg hf.abs
  constructor
  · intro h
    have habs : (fun x => |f x|) =ᵐ[μ] 0 := hiff.mp h
    filter_upwards [habs] with x hx
    exact abs_eq_zero.mp hx
  · intro h
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [h] with x hx
    simp [hx]

/--
Mathlib's Chebyshev/Markov inequality is naturally stated with `ENNReal`
measures and lower Lebesgue integrals.
-/
theorem chebyshev_lintegral {f : α → ENNReal} (hf : AEMeasurable f μ)
    {ε : ENNReal} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    μ {x | ε ≤ f x} ≤ (∫⁻ x, f x ∂μ) / ε := by
  exact MeasureTheory.meas_ge_le_lintegral_div hf hε0 hεtop

/--
The lecture statement
`μ {x | a ≤ |f x|} ≤ a⁻¹ ∫ |f| dμ` is formalized in `ENNReal` form.
The right-hand side uses the lower Lebesgue integral of `ENNReal.ofReal |f|`.
-/
theorem chebyshev_integrable_abs {f : α → ℝ} (hf : Integrable f μ)
    {a : ℝ} (ha : 0 < a) :
    μ {x | a ≤ |f x|} ≤
      (∫⁻ x, ENNReal.ofReal |f x| ∂μ) / ENNReal.ofReal a := by
  have hf_ae : AEMeasurable (fun x => ENNReal.ofReal |f x|) μ := by
    exact (hf.aestronglyMeasurable.aemeasurable.abs).ennreal_ofReal
  have h := MeasureTheory.meas_ge_le_lintegral_div (μ := μ)
      (f := fun x => ENNReal.ofReal |f x|) hf_ae
      (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
  have hset : {x | ENNReal.ofReal a ≤ ENNReal.ofReal |f x|} = {x | a ≤ |f x|} := by
    ext x
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg (f x))
  simpa [hset] using h

end OrderAndSize

/-! ## 5. Linearity -/

section Linearity

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_const_mul_real (c : ℝ) (f : α → ℝ) :
    (∫ x, c * f x ∂μ) = c * ∫ x, f x ∂μ := by
  simpa using MeasureTheory.integral_const_mul (μ := μ) c f

theorem integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : α → E) :
    (∫ x, c • f x ∂μ) = c • ∫ x, f x ∂μ := by
  exact MeasureTheory.integral_smul (μ := μ) c f

theorem integrable_add_real {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => f x + g x) μ := by
  simpa [Pi.add_apply] using hf.add hg

theorem integral_add_real {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, f x + g x ∂μ) =
      (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  simpa using MeasureTheory.integral_add (μ := μ) hf hg

theorem integral_neg_real (f : α → ℝ) :
    (∫ x, -f x ∂μ) = -∫ x, f x ∂μ := by
  simpa using MeasureTheory.integral_neg (μ := μ) (f := f)

theorem integral_sub_real {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, f x - g x ∂μ) =
      (∫ x, f x ∂μ) - ∫ x, g x ∂μ := by
  simpa using MeasureTheory.integral_sub (μ := μ) hf hg

theorem integral_finset_sum {ι : Type*} (s : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (∫ x, (∑ i ∈ s, f i x) ∂μ) =
      ∑ i ∈ s, (∫ x, f i x ∂μ) := by
  simpa using MeasureTheory.integral_finsetSum (μ := μ) s hf

end Linearity

/-! ## 6. Bounded functions on finite measure spaces -/

section BoundedOnFiniteMeasure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integrable_of_ae_abs_le_const [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, |f x| ≤ M) :
    Integrable f μ := by
  exact MeasureTheory.Integrable.of_bound hf M (by simpa [Real.norm_eq_abs] using hM)

theorem abs_integral_le_const_mul_measure [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, |f x| ≤ M) :
    |(∫ x, f x ∂μ)| ≤ M * μ.real Set.univ := by
  have hfi : Integrable f μ := integrable_of_ae_abs_le_const (μ := μ) hf hM
  have hle_abs : |(∫ x, f x ∂μ)| ≤ ∫ x, |f x| ∂μ :=
    abs_integral_le_integral_abs (μ := μ) f
  have hle_const : (∫ x, |f x| ∂μ) ≤ ∫ _x : α, M ∂μ := by
    exact MeasureTheory.integral_mono_ae hfi.abs
      (MeasureTheory.integrable_const (α := α) (μ := μ) M) hM
  calc
    |(∫ x, f x ∂μ)| ≤ ∫ x, |f x| ∂μ := hle_abs
    _ ≤ ∫ _x : α, M ∂μ := hle_const
    _ = M * μ.real Set.univ := by
      simp [MeasureTheory.integral_const, mul_comm]

end BoundedOnFiniteMeasure

end Chapter09
end NoteKsk
