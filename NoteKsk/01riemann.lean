/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
import NoteKsk.Defs

/-!
# Chapter 01: Riemann integration

This file follows `blueprint/src/chapters/01riemann.tex`.

It records the definition layer for one-dimensional Riemann and Darboux
integration.  Deferred chapter statements whose proofs are still placeholders
live in `NoteKsk/01riemann-statements.lean`, so downstream measure-theory files
can import this module without inheriting proof placeholders.
-/

noncomputable section

open scoped BigOperators Topology
open Set

namespace NoteKsk
namespace Chapter01

/-! ## Riemann sums -/

/-- Interior points of a partition of `[a,b]`, strictly increasing and inside the interval. -/
def IsValidPointList (a b : ℝ) (points : List ℝ) : Prop :=
  a ≤ b ∧ points.Pairwise (fun x y => x < y) ∧ ∀ x ∈ points, a < x ∧ x < b

/-- A finite partition of `[a,b]`, stored by its interior division points. -/
structure IntervalPartition where
  a : ℝ
  b : ℝ
  points : List ℝ
  valid : IsValidPointList a b points

namespace IntervalPartition

/-- Vertices of the partition, including the endpoints. -/
def vertices (P : IntervalPartition) : List ℝ :=
  P.a :: (P.points ++ [P.b])

/-- Adjacent subinterval endpoints of the partition. -/
def subintervals (P : IntervalPartition) : List (ℝ × ℝ) :=
  P.vertices.zip P.vertices.tail

/-- A tag function chooses one point in each subinterval, indexed from the left. -/
def IsTagged (P : IntervalPartition) (tags : ℕ → ℝ) : Prop :=
  ∀ item ∈ P.subintervals.zipIdx, tags item.2 ∈ Set.Icc item.1.1 item.1.2

/-- The partition with no interior division points. -/
def trivial (a b : ℝ) (hab : a ≤ b) : IntervalPartition where
  a := a
  b := b
  points := []
  valid := by
    simp [IsValidPointList, hab]

end IntervalPartition

/-- Mesh size of a partition: the maximum adjacent interval length. -/
def mesh (P : IntervalPartition) : ℝ :=
  (P.subintervals.map (fun uv => |uv.2 - uv.1|)).foldl max 0

/-- Riemann sum for a tagged partition. -/
def riemannSum (f : ℝ → ℝ) (P : IntervalPartition) (tags : ℕ → ℝ) : ℝ :=
  (P.subintervals.mapIdx fun i uv => f (tags i) * (uv.2 - uv.1)).sum

/-- `f` has Riemann integral `I` on `[a,b]`. -/
def HasRiemannIntegralOn (f : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P tags,
    P.a = a → P.b = b → P.IsTagged tags → mesh P < δ → |riemannSum f P tags - I| < ε

/-- Riemann integrability on `[a,b]`. -/
def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ I, HasRiemannIntegralOn f a b I

/-- The Riemann integral, when it exists; `0` outside the integrable case. -/
def riemannIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ I, HasRiemannIntegralOn f a b I then Classical.choose h else 0

/-! ## Darboux sums -/

/--
Supremum of `f` on a closed subinterval.

This is intentionally an extended-real-free lecture definition using mathlib's
totalized `sSup`; theorem statements supply the boundedness hypotheses needed
for the usual Darboux interpretation.
-/
def intervalSup (f : ℝ → ℝ) (u v : ℝ) : ℝ :=
  sSup (f '' Set.Icc u v)

/--
Infimum of `f` on a closed subinterval.

As with `intervalSup`, boundedness hypotheses are supplied by theorem
statements rather than by the definition itself.
-/
def intervalInf (f : ℝ → ℝ) (u v : ℝ) : ℝ :=
  sInf (f '' Set.Icc u v)

/-- Darboux upper sum. -/
def darbouxUpperSum (f : ℝ → ℝ) (P : IntervalPartition) : ℝ :=
  (P.subintervals.map fun uv => intervalSup f uv.1 uv.2 * (uv.2 - uv.1)).sum

/-- Darboux lower sum. -/
def darbouxLowerSum (f : ℝ → ℝ) (P : IntervalPartition) : ℝ :=
  (P.subintervals.map fun uv => intervalInf f uv.1 uv.2 * (uv.2 - uv.1)).sum

/-- Upper Darboux sums over all partitions of `[a,b]`. -/
def darbouxUpperValues (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {U | ∃ P : IntervalPartition, P.a = a ∧ P.b = b ∧ U = darbouxUpperSum f P}

/-- Lower Darboux sums over all partitions of `[a,b]`. -/
def darbouxLowerValues (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {L | ∃ P : IntervalPartition, P.a = a ∧ P.b = b ∧ L = darbouxLowerSum f P}

/-- Darboux upper integral: the infimum of upper sums. -/
def darbouxUpperIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf (darbouxUpperValues f a b)

/-- Darboux lower integral: the supremum of lower sums. -/
def darbouxLowerIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup (darbouxLowerValues f a b)

/-- Darboux integrability on `[a,b]`. -/
def DarbouxIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  darbouxUpperIntegral f a b = darbouxLowerIntegral f a b

/-- Darboux integral, represented by the upper integral. -/
def darbouxIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  darbouxUpperIntegral f a b

/-! ## Auxiliary predicates for deferred statements -/

/-- A lecture-level predicate for functions that are constant on each partition subinterval. -/
def PiecewiseConstantOnInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ P : IntervalPartition,
    P.a = a ∧ P.b = b ∧
      ∀ uv ∈ P.subintervals, ∃ c : ℝ, ∀ x ∈ Set.Icc uv.1 uv.2, f x = c

/-- A lecture-level predicate for functions continuous on each partition subinterval. -/
def PiecewiseContinuousOnInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ P : IntervalPartition,
    P.a = a ∧ P.b = b ∧
      ∀ uv ∈ P.subintervals, ContinuousOn f (Set.Icc uv.1 uv.2)

end Chapter01
end NoteKsk
