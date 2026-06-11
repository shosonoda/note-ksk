/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 01: Riemann integration

This file follows `blueprint/src/chapters/01riemann.tex`.

It records the lightweight Riemann/Darboux interface used by later chapters.
Deferred chapter statements whose proofs are still placeholders live in
`NoteKsk/01riemann-statements.lean`, so downstream measure-theory files can
import this module without inheriting proof placeholders.
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

end Chapter01
end NoteKsk
