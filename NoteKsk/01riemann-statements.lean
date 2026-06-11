/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.«01riemann»

/-!
# Chapter 01 deferred statements

This file contains the Chapter 01 statements whose proofs are not yet part of
the core dependency chain.  Later chapters should import `NoteKsk/01riemann.lean`
unless they explicitly need these placeholders.
-/

noncomputable section

open scoped BigOperators Topology
open Set

namespace NoteKsk
namespace Chapter01

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

/-- Piecewise constant functions are Riemann integrable. -/
theorem riemannIntegrable_piecewiseConstant
    {a b : ℝ} {f : ℝ → ℝ} (hf : PiecewiseConstantOnInterval f a b) :
    RiemannIntegrableOn f a b := by
  sorry

/-- Piecewise continuous functions are Riemann integrable. -/
theorem riemannIntegrable_piecewiseContinuous
    {a b : ℝ} {f : ℝ → ℝ} (hf : PiecewiseContinuousOnInterval f a b) :
    RiemannIntegrableOn f a b := by
  sorry

theorem riemann_sums_tendsto_integral
    {f : ℝ → ℝ} {a b : ℝ} (hf : RiemannIntegrableOn f a b)
    (P : ℕ → IntervalPartition) (tags : ℕ → ℕ → ℝ)
    (htagged : ∀ n, (P n).IsTagged (tags n))
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
