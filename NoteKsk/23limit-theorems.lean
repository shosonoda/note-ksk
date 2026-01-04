/-
  Lebesgue integral lecture notes (Lean 4 + Mathlib)

  * Dirichlet function is Lebesgue integrable (integral = 0).
  * Monotone / bounded / dominated convergence theorems as wrappers.

  References:
  - Tao, An Introduction to Measure Theory
  - Mathlib: MeasureTheory.Integral.*
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

namespace LebesgueIntegralNotes

/-!
# Dirichlet function (indicator of rationals) and Lebesgue integrability
-/

section Dirichlet

/-- The set of rationals, viewed as a subset of `ℝ`. -/
def ratSet : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))

/-- Dirichlet function: `1` on rationals, `0` on irrationals. -/
noncomputable def dirichlet : ℝ → ℝ :=
  ratSet.indicator (fun _ : ℝ => (1 : ℝ))

lemma ratSet_countable : (ratSet).Countable := by
  simpa [ratSet] using (Set.countable_range (fun q : ℚ => (q : ℝ)))

lemma measurableSet_ratSet : MeasurableSet ratSet := by
  -- Any countable set is measurable in a `MeasurableSingletonClass` space (e.g. `ℝ` with Borel).
  simpa using (ratSet_countable.measurableSet)

lemma measurable_dirichlet : Measurable dirichlet := by
  classical
  -- `indicator` of a measurable set of a measurable function is measurable.
  simpa [dirichlet] using
    ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator measurableSet_ratSet)

/-- `dirichlet = 0` almost everywhere for any measure without atoms. -/
lemma dirichlet_ae_eq_zero (μ : Measure ℝ) [NoAtoms μ] :
    dirichlet =ᶠ[ae μ] (0 : ℝ) := by
  have h : ∀ᵐ x ∂μ, x ∉ ratSet := (ratSet_countable.ae_notMem (μ := μ))
  filter_upwards [h] with x hx
  -- On the complement of `ratSet`, the indicator is zero.
  simpa [dirichlet, ratSet] using
    (Set.indicator_of_notMem hx (fun _ : ℝ => (1 : ℝ)))

/-- Dirichlet function is integrable (w.r.t. any no-atom measure). -/
theorem integrable_dirichlet (μ : Measure ℝ) [NoAtoms μ] :
    Integrable dirichlet μ := by
  have h0 : (fun x : ℝ => (0 : ℝ)) =ᶠ[ae μ] dirichlet :=
    (dirichlet_ae_eq_zero (μ := μ)).symm
  exact (integrable_zero : Integrable (fun x : ℝ => (0 : ℝ)) μ).congr h0

/-- The integral of the Dirichlet function is `0` (w.r.t. any no-atom measure). -/
theorem integral_dirichlet (μ : Measure ℝ) [NoAtoms μ] :
    (∫ x, dirichlet x ∂μ) = 0 := by
  exact integral_eq_zero_of_ae (dirichlet_ae_eq_zero (μ := μ))

/-- Specialization: on `[0,1]` with Lebesgue measure, the integral is `0`. -/
theorem integral_dirichlet_Icc :
    (∫ x in Set.Icc (0 : ℝ) 1, dirichlet x ∂volume) = 0 := by
  -- restricted Lebesgue measure is still atomless
  haveI : NoAtoms (volume.restrict (Set.Icc (0 : ℝ) 1)) := by infer_instance
  -- `∫ x in s, f x ∂μ` is definitionally `∫ x, f x ∂(μ.restrict s)`
  simpa using
    (integral_dirichlet (μ := volume.restrict (Set.Icc (0 : ℝ) 1)))

end Dirichlet

/-!
# Convergence theorems

We keep lecture-note style restatements as small wrappers around Mathlib lemmas.

* Monotone convergence: `lintegral` (ENNReal-valued, nonnegative world)
* Bounded convergence: finite measure, Bochner integral
* Dominated convergence: Bochner integral
-/

section ConvergenceTheorems

section Monotone

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable (f : ℕ → α → ENNReal)

/-- Monotone convergence theorem (Beppo Levi), measurable version. -/
theorem lintegral_iSup_eq
    (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f) :
    (∫⁻ x, (⨆ n, f n x) ∂μ) = ⨆ n, (∫⁻ x, f n x ∂μ) := by
  simpa using MeasureTheory.lintegral_iSup (μ := μ) hf hmono

/-- Monotone convergence theorem (Beppo Levi), a.e.-measurable version. -/
theorem lintegral_iSup_eq'
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    (∫⁻ x, (⨆ n, f n x) ∂μ) = ⨆ n, (∫⁻ x, f n x ∂μ) := by
  simpa using MeasureTheory.lintegral_iSup' (μ := μ) hf hmono

/-- Monotone convergence theorem, expressed as convergence of integrals. -/
theorem tendsto_lintegral_of_monotone
    {F : α → ENNReal}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (F x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (nhds (∫⁻ x, F x ∂μ)) := by
  simpa using
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone (μ := μ) hf hmono h_tendsto

end Monotone

section Bounded

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Bounded convergence theorem** (Bochner integral), sequence form.

This is a specialization of `MeasureTheory.tendsto_integral_filter_of_norm_le_const`
to `l = atTop`. -/
theorem tendsto_integral_of_bounded_convergence
    [IsFiniteMeasure μ]
    {F : ℕ → α → G} {f : α → G}
    (h_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∃ C : ℝ, ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  rcases h_bound with ⟨C, hC⟩
  have h_meas' :
      ∀ᶠ n in (atTop : Filter ℕ), AEStronglyMeasurable (F n) μ :=
    Filter.eventually_of_forall h_meas
  have h_bound' :
      ∃ C : ℝ, ∀ᶠ n in (atTop : Filter ℕ), ∀ᵐ x ∂μ, ‖F n x‖ ≤ C :=
    ⟨C, Filter.eventually_of_forall (fun n => hC n)⟩
  simpa using
    (MeasureTheory.tendsto_integral_filter_of_norm_le_const
      (μ := μ) (l := (atTop : Filter ℕ)) (F := F) (f := f)
      h_meas' h_bound' h_lim)

end Bounded

section Dominated

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Dominated convergence theorem** (Bochner integral), sequence form.

This is exactly `MeasureTheory.tendsto_integral_of_dominated_convergence`. -/
theorem tendsto_integral_of_dominated_convergence
    {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  simpa using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := μ) (F := F) (f := f)
      bound F_measurable bound_integrable h_bound h_lim)

end Dominated

end ConvergenceTheorems

end LebesgueIntegralNotes
