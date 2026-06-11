/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 10: Convergence theorems

This file follows `blueprint/src/chapters/10limits.tex`.

The main convergence theorems are stated in the form used by mathlib:

* monotone convergence, nonnegative series, and Fatou's lemma are formulated
  for the lower Lebesgue integral `∫⁻` of `ENNReal`-valued functions;
* dominated and bounded convergence are formulated for the Bochner integral;
* termwise integration is stated using `HasSum`/`tsum`;
* differentiation under the integral sign is the Fréchet/one-dimensional
  parametric integral theorem from mathlib.

These are stronger and more reusable than the informal real-valued lecture
statements.  The change of formulation is intentional: outside the construction
chapters we use mathlib's integral API directly.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open Set MeasureTheory Filter

namespace NoteKsk

namespace Chapter10

/-! ## 1. Monotone convergence and nonnegative series -/

section MonotoneConvergence

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Monotone convergence theorem for nonnegative functions, in `lintegral` form. -/
theorem monotone_convergence_lintegral {f : ℕ → α → ENNReal}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    (∫⁻ x, (⨆ n, f n x) ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ := by
  simpa using MeasureTheory.lintegral_iSup (μ := μ) hf hmono

/--
Almost-everywhere measurable version of monotone convergence.  This is often
the most convenient form for later convergence arguments.
-/
theorem monotone_convergence_lintegral_ae {f : ℕ → α → ENNReal}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    (∫⁻ x, (⨆ n, f n x) ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ := by
  simpa using MeasureTheory.lintegral_iSup' (μ := μ) hf hmono

/-- Monotone convergence expressed as convergence of the integrals. -/
theorem tendsto_lintegral_of_monotone {f : ℕ → α → ENNReal} {F : α → ENNReal}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := by
  simpa using
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      (μ := μ) hf hmono hlim

/-- Termwise integration for nonnegative series. -/
theorem lintegral_tsum {f : ι → α → ENNReal} [Countable ι]
    (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  simpa using MeasureTheory.lintegral_tsum (μ := μ) hf

end MonotoneConvergence

/-! ## 2. Fatou's lemma -/

section Fatou

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Fatou's lemma for `ENNReal`-valued functions. -/
theorem fatou_lintegral {f : ι → α → ENNReal} {l : Filter ι} [l.IsCountablyGenerated]
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, liminf (fun i => f i x) l ∂μ) ≤
      liminf (fun i => ∫⁻ x, f i x ∂μ) l := by
  simpa using MeasureTheory.lintegral_liminf_le (μ := μ) (u := l) hf

/-- Sequential Fatou lemma. -/
theorem fatou_lintegral_atTop {f : ℕ → α → ENNReal}
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤
      liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  exact fatou_lintegral (μ := μ) (l := atTop) hf

end Fatou

/-! ## 3. Dominated and bounded convergence -/

section DominatedConvergence

variable {α G : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup G]

/--
The limit function in dominated convergence has finite integral.  We keep the
a.e. strong measurability of the limit as an explicit hypothesis, because this
is the way Bochner integrability is represented in mathlib.
-/
theorem integrable_limit_of_dominated_convergence
    {F : ℕ → α → G} {f : α → G} {bound : α → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hbound_int : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Integrable f μ := by
  exact ⟨hf_meas,
    MeasureTheory.hasFiniteIntegral_of_dominated_convergence
      (μ := μ) hbound_int.hasFiniteIntegral hbound hlim⟩

variable [NormedSpace ℝ G]

/--
Dominated convergence theorem for Bochner integrals.

The lecture statement is real-valued; this mathlib form works for functions
with values in any real normed additive group.
-/
theorem tendsto_integral_of_dominated_convergence
    {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound_int : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := μ) (F := F) (f := f) bound hF_meas hbound_int hbound hlim

/-- Bounded convergence theorem on a finite measure space. -/
theorem tendsto_integral_of_bounded_convergence
    [IsFiniteMeasure μ] {F : ℕ → α → G} {f : α → G}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∃ C : ℝ, ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  rcases hbound with ⟨C, hC⟩
  refine MeasureTheory.tendsto_integral_filter_of_norm_le_const
    (μ := μ) (l := (atTop : Filter ℕ)) (F := F) (f := f) ?_ ?_ hlim
  · exact Eventually.of_forall hF_meas
  · exact ⟨C, Eventually.of_forall hC⟩

end DominatedConvergence

/-! ## 4. Termwise integration for signed series -/

section TermwiseIntegration

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Countable ι]

/--
Termwise integration under a dominated summability hypothesis.

This is the mathlib `HasSum` form of the lecture theorem
`∫ (∑ f_n) = ∑ ∫ f_n`.
-/
theorem hasSum_integral_of_dominated_convergence
    {F : ι → α → E} {f : α → E} (bound : ι → α → ℝ)
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound n x)
    (hbound_summable : ∀ᵐ x ∂μ, Summable fun n => bound n x)
    (hbound_int : Integrable (fun x => ∑' n, bound n x) μ)
    (hsum : ∀ᵐ x ∂μ, HasSum (fun n => F n x) (f x)) :
    HasSum (fun n => ∫ x, F n x ∂μ) (∫ x, f x ∂μ) := by
  simpa using
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := μ) (F := F) (f := f) bound hF_meas hbound
      hbound_summable hbound_int hsum

/-- A common sufficient condition for exchanging `tsum` and integral. -/
theorem integral_tsum_of_summable_integral_norm
    {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    (∑' i, ∫ x, F i x ∂μ) = ∫ x, ∑' i, F i x ∂μ := by
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := μ) hF_int hF_sum

end TermwiseIntegration

/-! ## 5. Parameter-dependent integrals -/

section ParameterIntegrals

variable {α X G : Type*} [MeasurableSpace α] {μ : Measure α}
variable [TopologicalSpace X] [FirstCountableTopology X]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Continuity under the integral sign by dominated convergence. -/
theorem continuous_integral_of_dominated
    {F : X → α → G} {bound : α → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a)
    (hbound_int : Integrable bound μ)
    (hcont : ∀ᵐ a ∂μ, Continuous fun x => F x a) :
    Continuous fun x : X => ∫ a, F x a ∂μ := by
  simpa using
    MeasureTheory.continuous_of_dominated
      (μ := μ) (F := F) (bound := bound) hF_meas hbound hbound_int hcont

/-- Pointwise continuity under the integral sign by dominated convergence. -/
theorem continuousAt_integral_of_dominated
    {F : X → α → G} {bound : α → ℝ} {x₀ : X}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a)
    (hbound_int : Integrable bound μ)
    (hcont : ∀ᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x : X => ∫ a, F x a ∂μ) x₀ := by
  simpa using
    MeasureTheory.continuousAt_of_dominated
      (μ := μ) (F := F) (bound := bound) (x₀ := x₀)
      hF_meas hbound hbound_int hcont

end ParameterIntegrals

/-! ## 6. Differentiation under the integral sign -/

section DifferentiationUnderIntegral

variable {α 𝕜 E H : Type*} [MeasurableSpace α] {μ : Measure α}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/--
Differentiation under the integral sign, Fréchet derivative form.

The lecture statement is the one-dimensional real special case.  Mathlib's
theorem works over `ℝ` or `ℂ` and for Fréchet derivatives.
-/
theorem hasFDerivAt_integral_under_dominated_loc_of_lip
    {F : H → α → E} {x₀ : H} {bound : α → ℝ} {s : Set H}
    {F' : α → H →L[𝕜] E}
    (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs (bound a)) (fun x : H => F x a) s)
    (hbound_int : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (fun x : H => F x a) (F' a) x₀) :
    Integrable F' μ ∧
      HasFDerivAt (fun x : H => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  simpa using
    hasFDerivAt_integral_of_dominated_loc_of_lip
      (μ := μ) (F := F) (x₀ := x₀) (bound := bound) (s := s) (F' := F')
      hs hF_meas hF_int hF'_meas h_lip hbound_int h_diff

/-- Differentiation under the integral sign, one-dimensional derivative form. -/
theorem hasDerivAt_integral_under_dominated_loc_of_lip
    {F : 𝕜 → α → E} {x₀ : 𝕜} {bound : α → ℝ} {s : Set 𝕜}
    {F' : α → E}
    (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 => F x a) s)
    (hbound_int : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivAt (fun x : 𝕜 => F x a) (F' a) x₀) :
    Integrable F' μ ∧
      HasDerivAt (fun x : 𝕜 => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  simpa using
    hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := μ) (F := F) (x₀ := x₀) (bound := bound) (s := s) (F' := F')
      hs hF_meas hF_int hF'_meas h_lip hbound_int h_diff

end DifferentiationUnderIntegral

end Chapter10
end NoteKsk
