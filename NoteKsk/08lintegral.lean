/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«07mble-funcs»

/-!
# Chapter 08: Lebesgue integral

This file follows `blueprint/src/chapters/08lintegral.tex`.

The formalization is aligned with mathlib's integral API.

* Nonnegative functions are represented as `α → ENNReal`, and their integral is
  mathlib's lower Lebesgue integral `∫⁻`.
* Signed functions are represented as real-valued functions `α → ℝ` with
  `Integrable f μ`, i.e. Bochner integrability.  This is the mathlib-native
  version of the lecture definition via positive and negative parts; the bridge
  theorem `integral_eq_positivePart_sub_negativePart` records the classical
  formula.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open Set MeasureTheory Filter

namespace NoteKsk
open Chapter07

namespace Chapter08

/-! ## 1. Integrals of nonnegative simple functions -/

section SimpleFunctions

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem simpleNNFun_measurable (s : SimpleNNFun α) :
    Measurable (fun x => s x) := by
  exact s.measurable

/--
Well-definedness of the simple-function integral is built into mathlib's bundled
`SimpleFunc`: if two bundled simple functions have the same pointwise values,
their integrals agree.
-/
theorem simpleLintegral_congr {s t : SimpleNNFun α}
    (hst : ∀ x, s x = t x) :
    simpleLintegral μ s = simpleLintegral μ t := by
  apply MeasureTheory.SimpleFunc.lintegral_congr
  filter_upwards [] with x
  exact hst x

theorem lintegralNN_eq_simple (s : SimpleNNFun α) :
    lintegralNN μ (fun x => s x) = simpleLintegral μ s := by
  simpa [lintegralNN, simpleLintegral] using
    (MeasureTheory.SimpleFunc.lintegral_eq_lintegral s μ)

theorem simpleLintegral_add (s t : SimpleNNFun α) :
    simpleLintegral μ (s + t) = simpleLintegral μ s + simpleLintegral μ t := by
  simpa [simpleLintegral] using
    (MeasureTheory.SimpleFunc.add_lintegral (μ := μ) s t)

theorem simpleLintegral_const_mul (c : ENNReal) (s : SimpleNNFun α) :
    simpleLintegral μ (MeasureTheory.SimpleFunc.const α c * s) =
      c * simpleLintegral μ s := by
  simpa [simpleLintegral] using
    (MeasureTheory.SimpleFunc.const_mul_lintegral (μ := μ) s c)

theorem simpleLintegral_mono {s t : SimpleNNFun α} (hst : s ≤ t) :
    simpleLintegral μ s ≤ simpleLintegral μ t := by
  simpa [simpleLintegral] using
    (MeasureTheory.SimpleFunc.lintegral_mono (μ := μ) hst le_rfl)

theorem lintegral_indicator_one_eq_measure {A : Set α} (hA : MeasurableSet A) :
    (∫⁻ x, A.indicator (fun _ : α => (1 : ENNReal)) x ∂μ) = μ A := by
  simpa using MeasureTheory.lintegral_indicator_one (μ := μ) hA

theorem lintegral_const_eq (c : ENNReal) :
    (∫⁻ _x : α, c ∂μ) = c * μ Set.univ := by
  simp

end SimpleFunctions

/-! ## 2. Nonnegative measurable functions and simple approximation -/

section NonnegativeIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegralNN_def (f : α → ENNReal) :
    lintegralNN μ f =
      ⨆ (g : SimpleNNFun α), ⨆ (_ : (g : α → ENNReal) ≤ f), g.lintegral μ := by
  simpa [lintegralNN] using (MeasureTheory.lintegral_def μ f)

theorem monotone_eapprox (f : α → ENNReal) :
    Monotone (MeasureTheory.SimpleFunc.eapprox f) :=
  MeasureTheory.SimpleFunc.monotone_eapprox f

theorem iSup_eapprox_apply {f : α → ENNReal} (hf : Measurable f) (x : α) :
    (⨆ n : ℕ, (MeasureTheory.SimpleFunc.eapprox f n) x) = f x := by
  simpa using MeasureTheory.SimpleFunc.iSup_eapprox_apply (f := f) hf x

theorem iSup_coe_eapprox {f : α → ENNReal} (hf : Measurable f) :
    (⨆ n : ℕ, (MeasureTheory.SimpleFunc.eapprox f n : α → ENNReal)) = f := by
  simpa using MeasureTheory.SimpleFunc.iSup_coe_eapprox (f := f) hf

theorem exists_monotone_simpleFunc_approx {f : α → ENNReal} (hf : Measurable f) :
    ∃ s : ℕ → SimpleNNFun α,
      Monotone s ∧ (∀ n x, s n x ≤ f x) ∧ (∀ x, (⨆ n : ℕ, s n x) = f x) := by
  refine ⟨MeasureTheory.SimpleFunc.eapprox f,
    MeasureTheory.SimpleFunc.monotone_eapprox f, ?_, ?_⟩
  · intro n x
    have hle : MeasureTheory.SimpleFunc.eapprox f n x ≤
        (⨆ k : ℕ, MeasureTheory.SimpleFunc.eapprox f k x) :=
      le_iSup (fun k : ℕ => MeasureTheory.SimpleFunc.eapprox f k x) n
    simpa [MeasureTheory.SimpleFunc.iSup_eapprox_apply (f := f) hf x] using hle
  · intro x
    simpa using MeasureTheory.SimpleFunc.iSup_eapprox_apply (f := f) hf x

theorem lintegralNN_eq_iSup_eapprox_lintegral {f : α → ENNReal} (hf : Measurable f) :
    lintegralNN μ f = ⨆ n : ℕ, (MeasureTheory.SimpleFunc.eapprox f n).lintegral μ := by
  simpa [lintegralNN] using
    MeasureTheory.lintegral_eq_iSup_eapprox_lintegral (μ := μ) (f := f) hf

theorem lintegral_iSup_of_measurable {f : ℕ → α → ENNReal}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    lintegralNN μ (fun x => ⨆ n : ℕ, f n x) =
      ⨆ n : ℕ, lintegralNN μ (f n) := by
  simpa [lintegralNN] using
    MeasureTheory.lintegral_iSup (μ := μ) (f := f) hf hmono

theorem lintegral_iSup_of_aeMeasurable {f : ℕ → α → ENNReal}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n : ℕ => f n x) :
    lintegralNN μ (fun x => ⨆ n : ℕ, f n x) =
      ⨆ n : ℕ, lintegralNN μ (f n) := by
  simpa [lintegralNN] using
    MeasureTheory.lintegral_iSup' (μ := μ) (f := f) hf hmono

theorem lintegralNN_add {f g : α → ENNReal} (hf : Measurable f) :
    lintegralNN μ (fun x => f x + g x) = lintegralNN μ f + lintegralNN μ g := by
  simpa [lintegralNN] using MeasureTheory.lintegral_add_left (μ := μ) hf g

theorem lintegralNN_const_mul {f : α → ENNReal} (c : ENNReal) (hf : Measurable f) :
    lintegralNN μ (fun x => c * f x) = c * lintegralNN μ f := by
  simpa [lintegralNN] using MeasureTheory.lintegral_const_mul (μ := μ) c hf

theorem lintegralNN_mono {f g : α → ENNReal} (hfg : f ≤ g) :
    lintegralNN μ f ≤ lintegralNN μ g := by
  simpa [lintegralNN] using MeasureTheory.lintegral_mono (μ := μ) hfg

theorem setLintegralNN_eq_indicator {A : Set α} (hA : MeasurableSet A) (f : α → ENNReal) :
    setLintegralNN μ A f = lintegralNN μ (A.indicator f) := by
  simpa [setLintegralNN, lintegralNN] using
    (MeasureTheory.lintegral_indicator (μ := μ) hA f).symm

theorem setLintegralNN_disjoint_union {A B : Set α} (hB : MeasurableSet B)
    (hAB : Disjoint A B) (f : α → ENNReal) :
    setLintegralNN μ (A ∪ B) f =
      setLintegralNN μ A f + setLintegralNN μ B f := by
  simpa [setLintegralNN] using
    MeasureTheory.lintegral_union (μ := μ) (f := f) hB hAB

end NonnegativeIntegral

/-! ## 3. Null sets and almost-everywhere invariance -/

section NullSetsAndAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem setLintegralNN_eq_zero_of_measure_zero {N : Set α} (hN : μ N = 0)
    (f : α → ENNReal) :
    setLintegralNN μ N f = 0 := by
  have hμ : μ.restrict N = 0 := Measure.restrict_eq_zero.mpr hN
  simp [setLintegralNN, hμ]

theorem lintegralNN_congr_ae {f g : α → ENNReal} (hfg : f =ᵐ[μ] g) :
    lintegralNN μ f = lintegralNN μ g := by
  simpa [lintegralNN] using MeasureTheory.lintegral_congr_ae (μ := μ) hfg

theorem lintegralNN_eq_zero_iff_ae_eq_zero {f : α → ENNReal} (hf : Measurable f) :
    lintegralNN μ f = 0 ↔ f =ᵐ[μ] 0 := by
  simpa [lintegralNN] using MeasureTheory.lintegral_eq_zero_iff (μ := μ) hf

end NullSetsAndAE

/-! ## 4. Signed real-valued functions -/

section SignedIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem positivePart_measurable {f : α → ℝ} (hf : Measurable f) :
    Measurable (positivePart f) := by
  simpa [positivePart] using hf.ennreal_ofReal

theorem negativePart_measurable {f : α → ℝ} (hf : Measurable f) :
    Measurable (negativePart f) := by
  simpa [negativePart] using hf.neg.ennreal_ofReal

theorem integral_eq_toReal_lintegral_ofReal {f : α → ℝ}
    (hf_nonneg : 0 ≤ᶠ[ae μ] f) (hf_strong : AEStronglyMeasurable f μ) :
    (∫ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  simpa using
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := μ) (f := f) hf_nonneg hf_strong

theorem integral_eq_positivePart_sub_negativePart {f : α → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) =
      (∫⁻ x, positivePart f x ∂μ).toReal -
        (∫⁻ x, negativePart f x ∂μ).toReal := by
  simpa [positivePart, negativePart] using
    MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (μ := μ) (f := f) hf

theorem lebesgueIntegral_eq_integral (f : α → ℝ) :
    lebesgueIntegral μ f = ∫ x, f x ∂μ := by
  rfl

theorem integrable_norm {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : Integrable f μ) :
    Integrable (fun x => ‖f x‖) μ := by
  exact hf.norm

theorem lebesgueIntegrable_iff_abs {f : α → ℝ}
    (hf_meas : AEStronglyMeasurable f μ) :
    LebesgueIntegrable μ f ↔ LebesgueIntegrable μ (fun x => |f x|) := by
  constructor
  · intro hf
    simpa [LebesgueIntegrable] using hf.abs
  · intro habs
    refine ⟨hf_meas, ?_⟩
    have hfi : HasFiniteIntegral (fun x => |f x|) μ := habs.hasFiniteIntegral
    simpa [HasFiniteIntegral, Real.norm_eq_abs] using hfi

theorem dominated_integrability {f g : α → ℝ}
    (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    Integrable f μ := by
  exact hg.mono' hf hfg

/--
In the lecture, signed measurable functions may be extended-real-valued and
integrability implies finiteness a.e.  Here signed integrable functions are
real-valued from the start, so the corresponding finiteness statement is
tautological.
-/
theorem integrable_real_finite_ae (f : α → ℝ) :
    ∀ᵐ x ∂μ, ((|f x| : ℝ) : EReal) < ⊤ := by
  filter_upwards [] with x
  simp

theorem integrableOn_of_measure_zero {N : Set α} (hN : μ N = 0) (f : α → ℝ) :
    IntegrableOn f N μ := by
  exact IntegrableOn.of_measure_zero hN

theorem setIntegral_eq_zero_of_measure_zero {N : Set α} (hN : μ N = 0) (f : α → ℝ) :
    (∫ x in N, f x ∂μ) = 0 := by
  exact MeasureTheory.setIntegral_measure_zero f hN

theorem signed_integral_congr_ae {f g : α → ℝ}
    (hf : Integrable f μ) (hfg : f =ᵐ[μ] g) :
    Integrable g μ ∧ (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  exact ⟨hf.congr hfg, MeasureTheory.integral_congr_ae hfg⟩

theorem integral_respects_ae_representatives {f g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  exact MeasureTheory.integral_congr_ae hfg

end SignedIntegral

/-! ## 5. Absolute continuity of the integral -/

section AbsoluteContinuity

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_absolute_continuity {f : α → ENNReal}
    (hfin : lintegralNN μ f ≠ ∞) {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ δ > 0, ∀ A : Set α, μ A < δ → setLintegralNN μ A f < ε := by
  simpa [lintegralNN, setLintegralNN] using
    MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt
      (μ := μ) (f := f) hfin hε

theorem integrable_abs_lintegral_ne_top {f : α → ℝ} (hf : Integrable f μ) :
    (∫⁻ x, ENNReal.ofReal |f x| ∂μ) ≠ ∞ := by
  have hfin :
      (∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) < ∞ :=
    (MeasureTheory.hasFiniteIntegral_iff_norm (μ := μ) f).mp hf.hasFiniteIntegral
  simpa [Real.norm_eq_abs] using hfin.ne

/--
Mathlib states the `ε`-`δ` absolute continuity theorem with `ENNReal` bounds
for measures.  This is the formal version of the lecture statement
`μ A < δ ⇒ ∫_A |f| < ε`.
-/
theorem integral_absolute_continuity {f : α → ℝ} (hf : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ A : Set α,
      μ A < δ → (∫⁻ x in A, ENNReal.ofReal |f x| ∂μ) < ENNReal.ofReal ε := by
  have hε_ne : ENNReal.ofReal ε ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hε).ne'
  simpa using
    lintegral_absolute_continuity
      (μ := μ) (f := fun x => ENNReal.ofReal |f x|)
      (integrable_abs_lintegral_ne_top (μ := μ) hf) hε_ne

theorem integral_absolute_continuity_filter {ι : Type*} {f : α → ℝ}
    (hf : Integrable f μ) {l : Filter ι} {A : ι → Set α}
    (hA : Tendsto (μ ∘ A) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in A i, f x ∂μ) l (𝓝 0) := by
  exact hf.tendsto_setIntegral_nhds_zero hA

end AbsoluteContinuity

/-! ## 6. Examples on the unit interval -/

section Examples

theorem rationalUnitInterval_countable :
    Chapter07.rationalUnitInterval.Countable := by
  exact Chapter07.rationalSet_countable.mono (by
    intro x hx
    exact hx.1)

theorem dirichletFunction01_ae_eq_zero :
    Chapter07.dirichletFunction01 =ᵐ[(volume : Measure ℝ)] 0 := by
  have hnot :
      ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Chapter07.rationalUnitInterval :=
    rationalUnitInterval_countable.ae_notMem (volume : Measure ℝ)
  filter_upwards [hnot] with x hx
  simp [Chapter07.dirichletFunction01, Set.indicator_of_notMem hx]

theorem integral_dirichletFunction01 :
    (∫ x, Chapter07.dirichletFunction01 x ∂(volume : Measure ℝ)) = 0 := by
  exact MeasureTheory.integral_eq_zero_of_ae dirichletFunction01_ae_eq_zero

theorem integral_dirichletFunction01_Icc :
    (∫ x in Set.Icc (0 : ℝ) 1, Chapter07.dirichletFunction01 x ∂(volume : Measure ℝ)) = 0 := by
  have hnot :
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)),
        x ∉ Chapter07.rationalUnitInterval :=
    rationalUnitInterval_countable.ae_notMem
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [hnot] with x hx
  simp [Chapter07.dirichletFunction01, Set.indicator_of_notMem hx]

/-- The irrational part of the unit interval. -/
def irrationalUnitInterval : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ Chapter07.rationalUnitInterval

/-- The indicator of the irrational part of `[0, 1]`. -/
def irrationalUnitIntervalIndicator : ℝ → ℝ :=
  irrationalUnitInterval.indicator fun _ => (1 : ℝ)

theorem irrationalUnitIntervalIndicator_ae_eq_one_on_Icc :
    irrationalUnitIntervalIndicator =ᵐ[(volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)]
      fun _ => (1 : ℝ) := by
  have hnot :
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)),
        x ∉ Chapter07.rationalUnitInterval :=
    rationalUnitInterval_countable.ae_notMem
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))
  have hmem :
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)),
        x ∈ Set.Icc (0 : ℝ) 1 :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hnot, hmem] with x hx hI
  have hxirr : x ∈ irrationalUnitInterval := ⟨hI, hx⟩
  simpa [irrationalUnitIntervalIndicator] using
    Set.indicator_of_mem hxirr (fun _ : ℝ => (1 : ℝ))

theorem volume_Icc_zero_one :
    (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) = 1 := by
  simp

theorem integral_irrationalUnitIntervalIndicator_Icc :
    (∫ x in Set.Icc (0 : ℝ) 1, irrationalUnitIntervalIndicator x ∂(volume : Measure ℝ)) =
      1 := by
  calc
    (∫ x in Set.Icc (0 : ℝ) 1, irrationalUnitIntervalIndicator x ∂(volume : Measure ℝ))
        = ∫ x in Set.Icc (0 : ℝ) 1, (1 : ℝ) ∂(volume : Measure ℝ) := by
          exact MeasureTheory.integral_congr_ae irrationalUnitIntervalIndicator_ae_eq_one_on_Icc
    _ = ((volume : Measure ℝ).real (Set.Icc (0 : ℝ) 1)) • (1 : ℝ) := by
          simp
    _ = 1 := by
          simp [MeasureTheory.measureReal_def]

end Examples

/-! ## 7. Relation with mathlib's Riemann box integral -/

section BoxRiemannBridge

variable {ι : Type*} [Fintype ι]

/--
Bounded a.e.-continuous functions on a rectangular box are Lebesgue integrable,
and mathlib's Riemann `BoxIntegral` has the same value as the Lebesgue integral.

This theorem deliberately uses mathlib's box-integral API,
`BoxIntegral.IntegrationParams.Riemann` and `BoxIntegral.BoxAdditiveMap.volume`.
It is not a theorem about the Chapter 01 lecture definitions
`Chapter01.RiemannIntegrableOn` or `Chapter01.riemannIntegral`.
-/
theorem boxRiemann_integrableOn_and_integral_eq_of_bounded_aeContinuous
    {I : BoxIntegral.Box ι} {f : (ι → ℝ) → ℝ}
    (hb : ∃ C : ℝ, ∀ x ∈ BoxIntegral.Box.Icc I, ‖f x‖ ≤ C)
    (hc : ∀ᵐ x ∂(volume : Measure (ι → ℝ)), ContinuousAt f x) :
    IntegrableOn f (I : Set (ι → ℝ)) (volume : Measure (ι → ℝ)) ∧
      BoxIntegral.integral I BoxIntegral.IntegrationParams.Riemann f
        BoxIntegral.BoxAdditiveMap.volume =
        ∫ x in (I : Set (ι → ℝ)), f x ∂(volume : Measure (ι → ℝ)) := by
  have hInt : IntegrableOn f (I : Set (ι → ℝ)) (volume : Measure (ι → ℝ)) := by
    constructor
    · let v := {x : (ι → ℝ) | ContinuousAt f x}
      have hv : AEStronglyMeasurable f ((volume : Measure (ι → ℝ)).restrict v) :=
        (continuousOn_of_forall_continuousAt fun _ h => h).aestronglyMeasurable
          (measurableSet_of_continuousAt f)
      refine hv.mono_measure (Measure.le_iff.2 fun s hs => ?_)
      repeat rw [Measure.restrict_apply hs]
      apply le_of_le_of_eq <| (volume : Measure (ι → ℝ)).mono s.inter_subset_left
      refine (measure_eq_measure_of_null_diff s.inter_subset_left ?_).symm
      rw [diff_self_inter, Set.diff_eq, ← nonpos_iff_eq_zero]
      grw [s.inter_subset_right]
      exact hc.le
    · have : IsFiniteMeasure ((volume : Measure (ι → ℝ)).restrict (BoxIntegral.Box.Icc I)) :=
        { measure_univ_lt_top := by
            simp [I.isCompact_Icc.measure_lt_top (μ := (volume : Measure (ι → ℝ)))] }
      have : IsFiniteMeasure ((volume : Measure (ι → ℝ)).restrict (I : Set (ι → ℝ))) :=
        isFiniteMeasure_of_le _
          ((volume : Measure (ι → ℝ)).restrict_mono BoxIntegral.Box.coe_subset_Icc le_rfl)
      obtain ⟨C, hC⟩ := hb
      refine .of_bounded (C := C) (Filter.eventually_iff_exists_mem.2 ?_)
      use I, self_mem_ae_restrict I.measurableSet_coe,
        fun y hy => hC y (I.coe_subset_Icc hy)
  have hBox : BoxIntegral.HasIntegral I BoxIntegral.IntegrationParams.Riemann f
      BoxIntegral.BoxAdditiveMap.volume
      (∫ x in (I : Set (ι → ℝ)), f x ∂(volume : Measure (ι → ℝ))) := by
    simpa [BoxIntegral.BoxAdditiveMap.volume] using
      (MeasureTheory.AEContinuous.hasBoxIntegral
        (μ := (volume : Measure (ι → ℝ)))
        (I := I) hb hc BoxIntegral.IntegrationParams.Riemann)
  exact ⟨hInt, hBox.integral_eq⟩

end BoxRiemannBridge

/-! ## 8. Improper-integral examples -/

section ImproperExamples

/-- The reciprocal function is not Lebesgue integrable on `[1, ∞)`. -/
theorem inv_not_lebesgue_integrable_on_Ici_one :
    ¬ IntegrableOn (fun x : ℝ => 1 / x) (Set.Ici (1 : ℝ)) (volume : Measure ℝ) := by
  simpa [one_div] using (not_integrableOn_Ici_inv (a := (1 : ℝ)))

/--
The standard example from the notes: `sin x / x` has a convergent improper
Riemann integral on `[1, ∞)`, but it is not Lebesgue integrable there.

The remaining analytic estimate is the lower-bound proof that
`|sin x / x|` is not integrable.  This theorem records the reduction from that
absolute-value estimate to the signed non-integrability statement.
-/
theorem sine_over_x_not_lebesgue_integrable_on_Ici_one :
    (¬ IntegrableOn (fun x : ℝ => |Real.sin x / x|)
      (Set.Ici (1 : ℝ)) (volume : Measure ℝ)) →
    ¬ IntegrableOn (fun x : ℝ => Real.sin x / x) (Set.Ici (1 : ℝ)) (volume : Measure ℝ) := by
  intro habs hsin
  exact habs (by
    simpa [Real.norm_eq_abs, abs_div] using hsin.norm)

end ImproperExamples

end Chapter08
end NoteKsk
