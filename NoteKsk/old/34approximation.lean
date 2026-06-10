/-
# Examples in Lp(R^d)

(1) Density: `C_c(R^d)` is dense in `L^p(R^d)` (for `p < ∞`), in the `eLpNorm`-approximation form.

(2) Convolution approximation (approximate identities / mollifiers):
    we set up the scaling `k_t(x) = k (t⁻¹ • x) / t^d` and the convolution operator.
    Mathlib provides strong pointwise / a.e. convergence statements for convolutions with bump functions.
    The `L^p` convergence statement for general `k ∈ L^1` is recorded as a blueprint stub.
-/

import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open scoped Topology ENNReal
open MeasureTheory Filter

namespace LebesgueLp

/-- Ambient space `ℝ^d` as a Euclidean space. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)
local notation "ℝ^" d => Rd d

/-- Lebesgue measure on `ℝ^d`. -/
local notation "μvol" => (MeasureTheory.volume : Measure (ℝ^d))

/-!
## 1. `C_c(ℝ^d)` is dense in `L^p(ℝ^d)`

We encode `C_c` as the *property* “continuous and compact support”.
This avoids committing to a particular bundled `C_c(α, β)` type in the statement,
and matches the approximation lemma already present in Mathlib.

Main Mathlib lemma:
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`.
-/

/-- The predicate “continuous with compact support”. -/
def IsCc {d : ℕ} (g : (ℝ^d) → ℝ) : Prop :=
  Continuous g ∧ HasCompactSupport g

theorem MemLp.exists_cc_approx
    {d : ℕ} {p : ℝ≥0∞} (hp : p ≠ ⊤)
    {f : (ℝ^d) → ℝ} (hf : MeasureTheory.MemLp f p (μvol (d:=d)))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : (ℝ^d) → ℝ,
      IsCc (d:=d) g ∧
      MeasureTheory.MemLp g p (μvol (d:=d)) ∧
      MeasureTheory.eLpNorm (f - g) p (μvol (d:=d)) ≤ ε := by
  -- This is essentially `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`,
  -- with the conjunctions rearranged to match `IsCc`.
  rcases
    (MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le
      (μ := (μvol (d:=d))) (p := p) hp hf hε)
    with ⟨g, hg_comp, hnorm, hg_cont, hg_mem⟩
  refine ⟨g, ?_, hg_mem, ?_⟩
  · exact ⟨hg_cont, hg_comp⟩
  · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hnorm

/-
A “density in `Lp`” corollary can be phrased in many ways.
For lecture notes, the `eLpNorm`-approximation lemma above is often the cleanest.
If you want a topological statement (`DenseRange` / `Dense`), you can build it from this lemma.
-/

/-!
## 2. Convolution approximation (mollifiers / approximate identities)

### 2.1 Scaling of an `L¹` kernel

Given `k : ℝ^d → ℝ` and `t : ℝ`, define

`k_t(x) = k (t⁻¹ • x) / t^d`.

(We will later use `t > 0`; we keep the definition total.)
-/

/-- Scaling of kernels: `k_t(x) = (t^d)⁻¹ * k(t⁻¹ • x)`. -/
def kernelScale {d : ℕ} (k : (ℝ^d) → ℝ) (t : ℝ) : (ℝ^d) → ℝ :=
  fun x => (t ^ d)⁻¹ * k (t⁻¹ • x)

/-!
### 2.2 Convolution (Mathlib’s definition)

Mathlib defines convolution of functions using the Bochner integral in
`Mathlib.Analysis.Convolution`.

For scalar-valued functions (multiplication as the bilinear map),
you can use `MeasureTheory.convolution` with `ContinuousLinearMap.mul`.
-/

/-- Convolution on `ℝ^d` with respect to Lebesgue measure (scalar case). -/
def conv {d : ℕ} (f g : (ℝ^d) → ℝ) : (ℝ^d) → ℝ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ) (μvol (d:=d))

notation:70 f " ⋆vol[" d "] " g => conv (d:=d) f g

/-
### 2.3 What Mathlib already provides (pointwise / a.e. convergence for bump-mollifiers)

Mathlib has strong theorems about convolution with a family of bump functions
whose supports shrink to `0` (pointwise at continuity points, and also a.e. for locally integrable
functions).

These live in `Mathlib.Analysis.Calculus.BumpFunction.Convolution`.
-/

/-
We *record* the statement as a lemma you can reference in your notes.
(Exact hypotheses may require some tuning depending on the version of Mathlib you’re on;
look up the `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` signature if needed.)
-/

-- Example stub showing how you would call the existing lemma:
-- (You will likely want `g : ℝ^d → F` for a normed space `F`, not just `ℝ`.)
--
-- theorem ae_convolution_tendsto_right_of_locallyIntegrable
--     {d : ℕ} {ι : Type*} {l : Filter ι}
--     (φ : ι → ContDiffBump (0 : ℝ^d))
--     {g : (ℝ^d) → ℝ} (hg : MeasureTheory.LocallyIntegrable g (μvol (d:=d)))
--     (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
--     ∀ᵐ x ∂(μvol (d:=d)),
--       Tendsto (fun i => ((φ i).normed (μvol (d:=d)) ⋆[lsmul ℝ ℝ, (μvol (d:=d))] g) x) l (𝓝 (g x)) := by
--   simpa using
--     (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
--       (μ := (μvol (d:=d))) (φ := φ) hg hφ)

/-!
### 2.4 Blueprint: `L^p` convergence of an approximate identity

What you asked for (Tao-style):

Let `k ∈ L¹(ℝ^d)` with `∫ k = 1`. Define `k_t` by scaling and set `k_t * f = (k_t ⋆ f)`.
Then `k_t * f → f` in `L^p` as `t → 0⁺` (for `1 ≤ p < ∞`).

A standard proof uses:
1. continuity of translations in `L^p`, i.e. `‖τ_y f - f‖_p → 0` as `y → 0`;
2. Minkowski integral inequality in `L^p` to bound
   `‖k_t * f - f‖_p ≤ ∫ ‖τ_y f - f‖_p |k_t(y)| dy`;
3. splitting the integral into `|y| < δ` and `|y| ≥ δ`, then using the tail of `k` in `L¹`.

Mathlib has the ingredients (Bochner integral, `Lp` is Banach, Hölder/Minkowski, Fubini/Tonelli),
but you may need to assemble several lemmas into the exact estimate above.

Below is a *blueprint placeholder* statement in the style of your notes.
Fill in the proof by introducing the translation action on `Lp` and proving the Minkowski-type bound.
-/

theorem tendsto_convolution_scaled_Lp
    {d : ℕ} {p : ℝ≥0∞}
    (hp1 : (1 : ℝ≥0∞) ≤ p) (hp : p ≠ ⊤)
    {k f : (ℝ^d) → ℝ}
    (hk : MeasureTheory.Integrable k (μvol (d:=d)))
    (hf : MeasureTheory.MemLp f p (μvol (d:=d)))
    (hk_one : (∫ x, k x ∂(μvol (d:=d))) = (1 : ℝ)) :
    Tendsto
      (fun t : ℝ => MeasureTheory.eLpNorm (fun x => (kernelScale (d:=d) k t ⋆vol[d] f) x - f x) p (μvol (d:=d)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- TODO (blueprint):
  -- 1) develop a lemma bounding `eLpNorm (k_t ⋆ f - f)` by an `L¹`-average of translation differences,
  -- 2) use translation continuity in `Lp`,
  -- 3) use tail control of `k` to finish.
  --
  -- This is the standard “approximate identity” argument in `L^p`.
  --
  -- For now, keep it as a blueprint goal.
  sorry

end LebesgueLp
