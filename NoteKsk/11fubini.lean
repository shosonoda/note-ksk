/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 11: Fubini, Tonelli, and change of variables

This file follows the streamlined chapter
`blueprint/src/chapters/11fubini02.tex`.

The lecture notes state the theorems first for Euclidean Lebesgue measure and
then for change of variables.  The formalization uses mathlib's native general
forms:

* product measures are `μ.prod ν`;
* Tonelli is `MeasureTheory.lintegral_prod`;
* Fubini is `MeasureTheory.integral_prod` and
  `MeasureTheory.integral_integral_swap`;
* change of variables is the Jacobian image formula from
  `Mathlib.MeasureTheory.Function.Jacobian`.

The Jacobian statements below are more general than the affine special cases in
the lecture notes.  Affine and linear transformations are obtained by
specializing the derivative to a constant linear map.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open Set MeasureTheory Filter

namespace NoteKsk

namespace Chapter11

/-! ## 1. Product measures and sections -/

section Sections

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The `x`-section of a subset of a product. -/
def xSection (E : Set (α × β)) (x : α) : Set β :=
  Prod.mk x ⁻¹' E

/-- The `y`-section of a subset of a product. -/
def ySection (E : Set (α × β)) (y : β) : Set α :=
  (fun x : α => (x, y)) ⁻¹' E

/-- The `x`-section of a function on a product. -/
def functionXSection (f : α × β → γ) (x : α) : β → γ :=
  fun y => f (x, y)

/-- The `y`-section of a function on a product. -/
def functionYSection (f : α × β → γ) (y : β) : α → γ :=
  fun x => f (x, y)

theorem measurableSet_xSection {E : Set (α × β)} (hE : MeasurableSet E) (x : α) :
    MeasurableSet (xSection E x) := by
  simpa [xSection] using measurable_prodMk_left hE

theorem measurableSet_ySection {E : Set (α × β)} (hE : MeasurableSet E) (y : β) :
    MeasurableSet (ySection E y) := by
  simpa [ySection] using measurable_prodMk_right hE

theorem measurable_functionXSection [MeasurableSpace γ] {f : α × β → γ}
    (hf : Measurable f) (x : α) :
    Measurable (functionXSection f x) := by
  simpa [functionXSection] using hf.comp measurable_prodMk_left

theorem measurable_functionYSection [MeasurableSpace γ] {f : α × β → γ}
    (hf : Measurable f) (y : β) :
    Measurable (functionYSection f y) := by
  simpa [functionYSection] using hf.comp measurable_prodMk_right

end Sections

section ProductMeasure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- Product measure on measurable sets, written using sections. -/
theorem productMeasure_apply [SFinite ν] {E : Set (α × β)} (hE : MeasurableSet E) :
    (μ.prod ν) E = ∫⁻ x, ν (xSection E x) ∂μ := by
  simpa [xSection] using MeasureTheory.Measure.prod_apply (μ := μ) (ν := ν) hE

/-- Product measure of a measurable rectangle. -/
theorem productMeasure_rectangle [SFinite ν] (A : Set α) (B : Set β) :
    (μ.prod ν) (A ×ˢ B) = μ A * ν B := by
  exact MeasureTheory.Measure.prod_prod (μ := μ) (ν := ν) A B

/-- Measurability of the section-measure function. -/
theorem measurable_measure_xSection [SFinite ν] {E : Set (α × β)} (hE : MeasurableSet E) :
    Measurable fun x : α => ν (xSection E x) := by
  simpa [xSection] using measurable_measure_prodMk_left (ν := ν) hE

end ProductMeasure

/-! ## 2. Tonelli's theorem -/

section Tonelli

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- Tonelli's theorem for nonnegative functions. -/
theorem tonelli_lintegral [SFinite ν]
    (f : α × β → ENNReal) (hf : AEMeasurable f (μ.prod ν)) :
    (∫⁻ z, f z ∂(μ.prod ν)) =
      ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  simpa using MeasureTheory.lintegral_prod (μ := μ) (ν := ν) f hf

/-- Tonelli's theorem with the order of integration reversed. -/
theorem tonelli_lintegral_symm [SFinite μ] [SFinite ν]
    (f : α × β → ENNReal) (hf : AEMeasurable f (μ.prod ν)) :
    (∫⁻ z, f z ∂(μ.prod ν)) =
      ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  simpa using MeasureTheory.lintegral_prod_symm (μ := μ) (ν := ν) f hf

/-- The inner integral in Tonelli is measurable. -/
theorem measurable_lintegral_section_right [SFinite ν]
    {f : α × β → ENNReal} (hf : Measurable f) :
    Measurable fun x : α => ∫⁻ y, f (x, y) ∂ν := by
  simpa using hf.lintegral_prod_right'

/-- Product form of Tonelli. -/
theorem lintegral_prod_mul [SFinite ν]
    {f : α → ENNReal} {g : β → ENNReal}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    (∫⁻ z, f z.1 * g z.2 ∂(μ.prod ν)) =
      (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simpa using MeasureTheory.lintegral_prod_mul (μ := μ) (ν := ν) hf hg

end Tonelli

/-! ## 3. Fubini's theorem -/

section Fubini

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [NormedAddCommGroup E]

/-- Almost-everywhere integrability of sections. -/
theorem ae_integrable_section_right [SFinite ν]
    {f : α × β → E} (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y : β => f (x, y)) ν := by
  exact ((MeasureTheory.integrable_prod_iff
    (μ := μ) (ν := ν) hf.aestronglyMeasurable).mp hf).1

variable [NormedSpace ℝ E]

/-- Fubini's theorem for Bochner integrals. -/
theorem fubini_integral_prod [SFinite μ] [SFinite ν]
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    (∫ z, f z ∂(μ.prod ν)) =
      ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  simpa using MeasureTheory.integral_prod (μ := μ) (ν := ν) f hf

/-- Fubini's theorem with the order of integration reversed. -/
theorem fubini_integral_prod_symm [SFinite μ] [SFinite ν]
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    (∫ z, f z ∂(μ.prod ν)) =
      ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  simpa using MeasureTheory.integral_prod_symm (μ := μ) (ν := ν) f hf

/-- Exchange of iterated integrals for an integrable function. -/
theorem integral_integral_swap [SFinite μ] [SFinite ν]
    {f : α → β → E} (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) =
      ∫ y, ∫ x, f x y ∂μ ∂ν := by
  simpa using MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) hf

/-- Integrability of the function obtained by integrating the right section. -/
theorem integrable_integral_section_right [SFinite ν]
    {f : α × β → E} (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x : α => ∫ y : β, f (x, y) ∂ν) μ := by
  exact hf.integral_prod_left

/-- Integrability of the function obtained by integrating the left section. -/
theorem integrable_integral_section_left [SFinite μ] [SFinite ν]
    {f : α × β → E} (hf : Integrable f (μ.prod ν)) :
    Integrable (fun y : β => ∫ x : α, f (x, y) ∂μ) ν := by
  exact hf.integral_prod_right

/-- Product form of Fubini for scalar-valued functions. -/
theorem integral_prod_mul [SFinite μ] [SFinite ν] {L : Type*} [RCLike L]
    (f : α → L) (g : β → L) :
    (∫ z : α × β, f z.1 * g z.2 ∂(μ.prod ν)) =
      (∫ x, f x ∂μ) * ∫ y, g y ∂ν := by
  simpa using MeasureTheory.integral_prod_mul (μ := μ) (ν := ν) f g

end Fubini

/-! ## 4. Change of variables -/

section ChangeOfVariables

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/--
Jacobian change-of-variables formula for nonnegative functions.

This is the formal replacement for the lecture's affine/linear change of
variables statements.  Those are obtained by taking `f` to be an affine map and
`f'` to be its constant derivative.
-/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul
    {s : Set E} {φ : E → E} {φ' : E → E →L[ℝ] E}
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x)
    (hφ : InjOn φ s) (g : E → ENNReal) :
    (∫⁻ x in φ '' s, g x ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(φ' x).det| * g (φ x) ∂μ := by
  simpa using
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μ := μ) hs hφ' hφ g

/--
Jacobian change-of-variables formula for Bochner integrals.

The lecture statement for a diffeomorphism is represented here by mathlib's
image formula on a measurable set with an injectivity hypothesis.
-/
theorem integral_image_eq_integral_abs_det_fderiv_smul
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {φ : E → E} {φ' : E → E →L[ℝ] E}
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x)
    (hφ : InjOn φ s) (g : E → F) :
    (∫ x in φ '' s, g x ∂μ) =
      ∫ x in s, |(φ' x).det| • g (φ x) ∂μ := by
  simpa using
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := μ) hs hφ' hφ g

end ChangeOfVariables

end Chapter11
end NoteKsk
