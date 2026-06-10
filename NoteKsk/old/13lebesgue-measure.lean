/-
Lecture notes (Lebesgue integration / measure theory) in Lean4 + mathlib.

This file: motivation and formal core for
* (Lebesgue-style) “inner measure” viewpoint of measurability
* (Carathéodory-style) measurability and the Carathéodory extension `OuterMeasure.toMeasure`

References (informal): Tao, *An Introduction to Measure Theory*; and mathlib’s
`MeasureTheory.OuterMeasure.Caratheodory` + `MeasureTheory.Measure.MeasureSpace`.
-/

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.Compactness.Compact

open scoped BigOperators
open Set
open MeasureTheory

namespace LebesgueNotes

/-!
# Lebesgue-style vs. Carathéodory-style measurability

## Big picture

* **Lebesgue-style** (historical / intuitive): start from an outer measure `m : OuterMeasure α`,
  define an “inner approximation from inside” by supremum over *compact subsets*.
  A set is “measurable” if outer and inner values agree.

  This depends on having a topology (compact sets).

* **Carathéodory-style** (axiomatic / general): define measurability by the splitting identity
  `m t = m (t ∩ s) + m (t \ s)` for all `t`. This produces a σ-algebra `m.caratheodory`,
  and an associated measure obtained by restricting the outer measure (`OuterMeasure.toMeasure`).

In classical Lebesgue measure on `ℝ`/`ℝⁿ`, these viewpoints are equivalent once regularity
(inner/outer approximation) is established. In this note, we set up both notions in Lean.
-/

/-!
## 1. Lebesgue-style: inner approximation by compact subsets

Given an outer measure `m` on a topological space, define

`inner m s := sup { m K | K ⊆ s, K compact }`.

Then `inner m s ≤ m s` always holds by monotonicity.
If `s` itself is compact, then the supremum contains `K = s`, hence `inner m s = m s`.

We may *define* a (Lebesgue-flavored) notion of measurability by the equality `m s = inner m s`.
This is not a σ-algebra for an arbitrary outer measure; but for concrete outer measures (like
Lebesgue outer measure on `ℝⁿ`) it becomes equivalent to Carathéodory measurability.
-/

section LebesgueStyle

universe u
variable {α : Type u} [TopologicalSpace α]
variable (m : OuterMeasure α)

/-- The type of compact subsets of a set `s`. -/
def CompactSubset (s : Set α) : Type u :=
  { K : Set α // IsCompact K ∧ K ⊆ s }

/--
Lebesgue-style “inner” approximation of an outer measure by compact subsets:
`inner m s = sup_{K ⊆ s, K compact} m K`.
-/
noncomputable def inner (s : Set α) : ENNReal :=
  ⨆ K : CompactSubset (α := α) s, m K.1

/-- `inner m s ≤ m s` by monotonicity of the outer measure. -/
theorem inner_le (s : Set α) : inner m s ≤ m s := by
  classical
  refine iSup_le ?_
  intro K
  -- `K.2.2 : K ⊆ s`
  exact MeasureTheory.measure_mono (μ := m) K.2.2

/-- Monotonicity of `inner`: if `s ⊆ t` then `inner m s ≤ inner m t`. -/
theorem inner_mono {s t : Set α} (hst : s ⊆ t) : inner m s ≤ inner m t := by
  classical
  refine iSup_le ?_
  intro K
  -- push the same compact set into the bigger index set
  refine le_iSup_of_le ⟨K.1, K.2.1, subset_trans K.2.2 hst⟩ ?_
  exact le_rfl

/--
If `s` is compact, then `inner m s = m s` because the supremum includes `K = s`.
-/
theorem inner_eq_of_isCompact {s : Set α} (hs : IsCompact s) : inner m s = m s := by
  classical
  have hle : inner m s ≤ m s := inner_le (m := m) s
  have hge : m s ≤ inner m s := by
    refine le_iSup_of_le ⟨s, hs, subset_rfl⟩ ?_
    exact le_rfl
  exact le_antisymm hle hge

/-- Lebesgue-style (topological) measurability: outer measure equals inner approximation. -/
def IsLebesgueMeasurable (s : Set α) : Prop :=
  m s = inner m s

/-- Every compact set is Lebesgue-measurable in the above sense. -/
theorem isLebesgueMeasurable_of_isCompact {s : Set α} (hs : IsCompact s) :
    IsLebesgueMeasurable (m := m) s := by
  -- `inner m s = m s`, so `m s = inner m s` holds trivially.
  simpa [IsLebesgueMeasurable, inner_eq_of_isCompact (m := m) hs]

/-- Finite unions of compact sets are compact, hence Lebesgue-measurable. -/
theorem isLebesgueMeasurable_union_of_isCompact {s t : Set α}
    (hs : IsCompact s) (ht : IsCompact t) :
    IsLebesgueMeasurable (m := m) (s ∪ t) := by
  -- `IsCompact.union hs ht : IsCompact (s ∪ t)`
  exact isLebesgueMeasurable_of_isCompact (m := m) (IsCompact.union hs ht)

/-!
### A “TODO” bridge theorem (to be proved later)

For the *specific* outer measure that yields Lebesgue measure on `ℝⁿ`,
one shows regularity (approximation by compact/open sets), and then proves that
the Lebesgue-style definition coincides with Carathéodory measurability.

We intentionally leave it as a theorem statement (blueprint placeholder).
-/

/-- Placeholder: for the Lebesgue outer measure on `ℝⁿ`, these notions coincide. -/
theorem lebesgueStyle_eq_caratheodoryStyle
    (m : OuterMeasure α) :
    True := by
  trivial

end LebesgueStyle

/-!
## 2. Carathéodory-style: criterion, σ-algebra, and extension to a measure

Mathlib already packages the Carathéodory theory:

* `m.IsCaratheodory s` is the criterion `∀ t, m t = m (t ∩ s) + m (t \ s)`.
* `m.caratheodory : MeasurableSpace α` is the σ-algebra of Carathéodory-measurable sets.
* If you have a measurable space `ms` such that `ms ≤ m.caratheodory`,
  then `m.toMeasure h : Measure α` is the measure obtained by restricting `m`
  to the σ-algebra.

The key simp lemma is `MeasureTheory.toMeasure_apply`.
-/

section CaratheodoryStyle

universe u
variable {α : Type u}
variable (m : OuterMeasure α)

/-- Carathéodory measurability predicate (mathlib definition). -/
abbrev IsCaratheodory (s : Set α) : Prop :=
  m.IsCaratheodory s

/-- The Carathéodory σ-algebra associated to `m`. -/
abbrev caratheodoryMS : MeasurableSpace α :=
  m.caratheodory

/--
Unbundled version: a set is measurable in the Carathéodory measurable space iff it satisfies
Carathéodory’s splitting identity (for all `t`).

This is just `OuterMeasure.isCaratheodory_iff` with the ambient measurable space
set to `m.caratheodory`.
-/
theorem measurableSet_caratheodory_iff (s : Set α) :
    @MeasurableSet α (m.caratheodory) s ↔ ∀ t : Set α, m t = m (t ∩ s) + m (t \ s) := by
  classical
  -- `OuterMeasure.isCaratheodory_iff` is stated with `MeasurableSet` in the local instance
  -- `m.caratheodory`; we introduce that instance and `simpa`.
  letI : MeasurableSpace α := m.caratheodory
  simpa using (MeasureTheory.OuterMeasure.isCaratheodory_iff (m := m) (s := s))

/--
Inequality-only form of Carathéodory’s criterion:
`MeasurableSet s ↔ ∀ t, m(t∩s) + m(t\s) ≤ m t`.
-/
theorem measurableSet_caratheodory_iff_le (s : Set α) :
    @MeasurableSet α (m.caratheodory) s ↔ ∀ t : Set α, m (t ∩ s) + m (t \ s) ≤ m t := by
  classical
  letI : MeasurableSpace α := m.caratheodory
  simpa using (MeasureTheory.OuterMeasure.isCaratheodory_iff_le (m := m) (s := s))

/-- Closure under complement for `m.IsCaratheodory`. -/
theorem isCaratheodory_compl {s : Set α} (hs : IsCaratheodory (m := m) s) :
    IsCaratheodory (m := m) sᶜ := by
  simpa [IsCaratheodory] using (MeasureTheory.OuterMeasure.isCaratheodory_compl (m := m) hs)

/-- Closure under countable unions for `m.IsCaratheodory`. -/
theorem isCaratheodory_iUnion {s : ℕ → Set α} (hs : ∀ n, IsCaratheodory (m := m) (s n)) :
    IsCaratheodory (m := m) (⋃ n, s n) := by
  simpa [IsCaratheodory] using (MeasureTheory.OuterMeasure.isCaratheodory_iUnion (m := m) hs)

/-!
### Carathéodory extension: `OuterMeasure.toMeasure`

`OuterMeasure.toMeasure` needs an ambient measurable space `ms` and an inclusion proof
`h : ms ≤ m.caratheodory`.

The most canonical choice is `ms = m.caratheodory` itself, with `h = le_rfl`.
This produces a measure on the Carathéodory σ-algebra.
-/

/-- The measure induced on the Carathéodory σ-algebra of `m`. -/
noncomputable def toMeasureCaratheodory : @Measure α m.caratheodory :=
  m.toMeasure (by
    simpa using (le_rfl : m.caratheodory ≤ m.caratheodory))

/--
On Carathéodory-measurable sets, `toMeasureCaratheodory` agrees with the outer measure `m`.
-/
theorem toMeasureCaratheodory_apply {s : Set α} (hs : @MeasurableSet α m.caratheodory s) :
    (toMeasureCaratheodory (m := m)) s = m s := by
  -- `MeasureTheory.toMeasure_apply` is the key lemma.
  simpa [toMeasureCaratheodory] using
    (MeasureTheory.toMeasure_apply (m := m)
      (h := (le_rfl : m.caratheodory ≤ m.caratheodory)) hs)

/--
The outer measure associated to `toMeasureCaratheodory` is the trim of the original outer measure.
-/
theorem toMeasureCaratheodory_toOuterMeasure :
    (toMeasureCaratheodory (m := m)).toOuterMeasure = m.trim := by
  simpa [toMeasureCaratheodory] using
    (MeasureTheory.toMeasure_toOuterMeasure (m := m)
      (h := (le_rfl : m.caratheodory ≤ m.caratheodory)))

end CaratheodoryStyle

/-!
## 3. Carathéodory extension API on an *ambient* measurable space

Often we already have a measurable space `ms` (e.g. `borel α`), and build an outer measure `m`
such that all measurable sets are Carathéodory-measurable: `ms ≤ m.caratheodory`.
Then `m.toMeasure h` is a measure on `ms`.

This is exactly the Carathéodory extension step used repeatedly in mathlib.
-/

section CaratheodoryExtensionAPI

universe u
variable {α : Type u} [MeasurableSpace α]
variable (m : OuterMeasure α)

/-- Turn an outer measure into a measure, assuming all measurable sets are Carathéodory-measurable. -/
noncomputable def toMeasureFromOuter
    (h : (‹MeasurableSpace α› : MeasurableSpace α) ≤ m.caratheodory) : Measure α :=
  m.toMeasure h

/-- On measurable sets, the induced measure agrees with the outer measure. -/
theorem toMeasureFromOuter_apply
    {h : (‹MeasurableSpace α› : MeasurableSpace α) ≤ m.caratheodory}
    {s : Set α} (hs : MeasurableSet s) :
    (toMeasureFromOuter (m := m) h) s = m s := by
  simpa [toMeasureFromOuter] using (MeasureTheory.toMeasure_apply (m := m) (h := h) hs)

/-- The outer measure is always bounded above by the induced measure (on all sets). -/
theorem le_toMeasureFromOuter_apply
    (h : (‹MeasurableSpace α› : MeasurableSpace α) ≤ m.caratheodory) (s : Set α) :
    m s ≤ (toMeasureFromOuter (m := m) h) s := by
  simpa [toMeasureFromOuter] using (MeasureTheory.le_toMeasure_apply (m := m) (h := h) s)

end CaratheodoryExtensionAPI

/-!
## 4. (Optional) Mathlib’s “content → innerContent → outerMeasure → measure” pipeline

This is the route often used to build regular Borel measures:
start with a `Content α` on compact sets, define an inner content on open sets,
then define an outer measure, prove Borel sets are Carathéodory-measurable, and extend.

For Lebesgue measure on `ℝⁿ`, one can package “volume on boxes” into a content-like object
(or use existing constructions in `Mathlib`), and then proceed via this pipeline.

We record the key objects as Lean definitions (no new proofs).
-/

section ContentPipeline

universe u
variable {α : Type u} [TopologicalSpace α] [T2Space α]
variable (c : MeasureTheory.Content α)

/-- The inner content on opens: supremum of `c` over compact subsets. -/
noncomputable def innerContentOnOpens : MeasureTheory.Opens α → ENNReal :=
  c.innerContent

/-- The induced outer measure from the content. -/
noncomputable def outerMeasureOfContent : OuterMeasure α :=
  c.outerMeasure

/--
A key fact in mathlib’s pipeline: for a content, all Borel sets are Carathéodory-measurable
for the induced outer measure.
-/
theorem borel_le_caratheodory_outerMeasureOfContent :
    borel α ≤ (outerMeasureOfContent (c := c)).caratheodory :=
  c.borel_le_caratheodory

/-- The Borel measure associated to a content (`c.measure` in mathlib). -/
noncomputable def measureOfContent : Measure α :=
  c.measure

end ContentPipeline

end LebesgueNotes
