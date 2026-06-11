/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 01: Riemann integration

This file follows `blueprint/src/chapters/01riemann.tex`.

For now it records a lightweight interface for partitions, Riemann sums,
Darboux sums, and the main comparison theorems.  The definitions are intentionally
kept simple so that Chapters 2 and 3 can already depend on their statements.
-/

noncomputable section

open scoped BigOperators Topology
open Set

namespace NoteKsk
namespace Chapter01

/-! ## Riemann sums -/

/-- A finite partition of `[a,b]`; the ordering conditions are TODO data for now. -/
structure IntervalPartition where
  a : ℝ
  b : ℝ
  points : List ℝ
  valid : Prop := True

/-- Mesh size of a partition.  TODO: replace by the maximum adjacent gap. -/
def mesh (_P : IntervalPartition) : ℝ := 0

/-- Riemann sum for a tagged partition.  TODO: replace by the actual finite sum. -/
def riemannSum (_f : ℝ → ℝ) (_P : IntervalPartition) (_tags : ℕ → ℝ) : ℝ := 0

/-- `f` has Riemann integral `I` on `[a,b]`. -/
def HasRiemannIntegralOn (f : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P tags,
    P.a = a → P.b = b → mesh P < δ → |riemannSum f P tags - I| < ε

/-- Riemann integrability on `[a,b]`. -/
def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ I, HasRiemannIntegralOn f a b I

/-- The Riemann integral, when it exists; `0` outside the integrable case. -/
def riemannIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ I, HasRiemannIntegralOn f a b I then Classical.choose h else 0

/-! ## Darboux sums -/

/-- Darboux upper sum.  TODO: replace by the sum of coordinate suprema. -/
def darbouxUpperSum (_f : ℝ → ℝ) (_P : IntervalPartition) : ℝ := 0

/-- Darboux lower sum.  TODO: replace by the sum of coordinate infima. -/
def darbouxLowerSum (_f : ℝ → ℝ) (_P : IntervalPartition) : ℝ := 0

/-- Darboux upper integral.  TODO: replace by the infimum over partitions. -/
def darbouxUpperIntegral (_f : ℝ → ℝ) (_a _b : ℝ) : ℝ := 0

/-- Darboux lower integral.  TODO: replace by the supremum over partitions. -/
def darbouxLowerIntegral (_f : ℝ → ℝ) (_a _b : ℝ) : ℝ := 0

/-- Darboux integrability on `[a,b]`. -/
def DarbouxIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ P : IntervalPartition,
    P.a = a ∧ P.b = b ∧ darbouxUpperSum f P - darbouxLowerSum f P < ε

/-- Darboux integral, represented by the upper integral. -/
def darbouxIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  darbouxUpperIntegral f a b

/-! ## Basic chapter statements -/

theorem riemann_integrable_iff_darboux_integrable
    (f : ℝ → ℝ) (a b : ℝ) :
    RiemannIntegrableOn f a b ↔ DarbouxIntegrableOn f a b := by
  sorry

theorem riemannIntegral_eq_darbouxIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hf : RiemannIntegrableOn f a b) :
    riemannIntegral f a b = darbouxIntegral f a b := by
  sorry

theorem riemannIntegrable_const (a b c : ℝ) :
    RiemannIntegrableOn (fun _ => c) a b := by
  sorry

theorem riemannIntegral_const (a b c : ℝ) :
    riemannIntegral (fun _ => c) a b = c * (b - a) := by
  sorry

theorem riemannIntegrable_id (a b : ℝ) :
    RiemannIntegrableOn (fun x => x) a b := by
  sorry

theorem riemannIntegral_id (a b : ℝ) :
    riemannIntegral (fun x => x) a b = (b ^ 2 - a ^ 2) / 2 := by
  sorry

theorem riemannIntegrable_of_continuousOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    RiemannIntegrableOn f a b := by
  sorry

/-- Piecewise constant functions are Riemann integrable.  The precise encoding is TODO. -/
theorem riemannIntegrable_piecewiseConstant
    (a b : ℝ) (f : ℝ → ℝ) :
    RiemannIntegrableOn f a b := by
  sorry

/-- Piecewise continuous functions are Riemann integrable.  The precise encoding is TODO. -/
theorem riemannIntegrable_piecewiseContinuous
    (a b : ℝ) (f : ℝ → ℝ) :
    RiemannIntegrableOn f a b := by
  sorry

theorem riemann_sums_tendsto_integral
    {f : ℝ → ℝ} {a b : ℝ} (hf : RiemannIntegrableOn f a b)
    (P : ℕ → IntervalPartition) (tags : ℕ → ℕ → ℝ)
    (hmesh : Filter.Tendsto (fun n => mesh (P n)) Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n => riemannSum f (P n) (tags n))
      Filter.atTop
      (𝓝 (riemannIntegral f a b)) := by
  sorry

theorem fundamental_theorem_of_calculus_for_riemann
    {F f : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (Set.Icc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x)
    (hfc : ContinuousOn f (Set.Icc a b)) :
    RiemannIntegrableOn f a b ∧ riemannIntegral f a b = F b - F a := by
  sorry

/-! ## Non-integrable examples -/

/-- Dirichlet function: `1` on rational points and `0` elsewhere. -/
def dirichlet (x : ℝ) : ℝ :=
  by
    classical
    exact if x ∈ Set.range Rat.cast then 1 else 0

theorem not_riemannIntegrable_dirichlet :
    ¬ RiemannIntegrableOn dirichlet 0 1 := by
  sorry

theorem not_riemannIntegrable_of_unboundedOn
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ¬ Bornology.IsBounded (f '' Set.Icc a b)) :
    ¬ RiemannIntegrableOn f a b := by
  sorry

end Chapter01
end NoteKsk
