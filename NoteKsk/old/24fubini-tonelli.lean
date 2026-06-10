/-
  Lebesgue積分論 講義ノート（Lean4 + Mathlib）
  章：完備化・絶対可積分・積測度・Fubini–Tonelli・積分記号下の微分
-/

import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral

open scoped BigOperators Topology ENNReal
open MeasureTheory

namespace LebesgueLecture

/-!
## 1. 測度の完備化（completion）

Mathlibでは，測度 `μ : Measure α` から
`NullMeasurableSpace α μ` 上の完備測度 `μ.completion` を作る。

- `μ.completion` は完備（`IsComplete` インスタンス）
- 集合関数としては `μ` と一致（`completion_apply`）
- a.e. フィルタも一致（`ae_completion`）
-/

section Completion

variable {α : Type*} [MeasurableSpace α]

/-- ノート側の記法：`μᶜ` を `μ.completion` の略記にする。 -/
abbrev completion (μ : Measure α) : Measure (NullMeasurableSpace α μ) := μ.completion

notation μ "ᶜ" => completion (μ := μ)

variable (μ : Measure α)

instance : (μᶜ).IsComplete := by
  -- Mathlib: `Measure.completion.isComplete`
  infer_instance

@[simp] theorem completion_apply (s : Set α) : μᶜ s = μ s := by
  -- Mathlib: `Measure.completion_apply`
  simpa [completion] using (MeasureTheory.Measure.completion_apply (μ := μ) s)

@[simp] theorem ae_completion : (ae (μᶜ)) = ae μ := by
  -- Mathlib: `Measure.ae_completion`
  simpa [completion] using (MeasureTheory.Measure.ae_completion (μ := μ))

/-- 完備化した測度では，`μ`-零集合は可測になる（典型例）。 -/
theorem measurableSet_of_null_in_completion {s : Set α} (hs : μ s = 0) :
    MeasurableSet (s : Set (NullMeasurableSpace α μ)) := by
  -- `μᶜ s = 0` を作って完備性から measurability を得る
  have hs' : (μᶜ) s = 0 := by
    calc
      (μᶜ) s = μ s := by simpa using (completion_apply (μ := μ) s)
      _ = 0 := hs
  exact MeasureTheory.measurableSet_of_null (μ := (μᶜ)) hs'

end Completion


/-!
## 2. 可積分性と（教科書的な意味での）絶対可積分性

Mathlibの `Integrable f μ` は *最初から*
「`f` が a.e. 強可測で，`∫ ‖f‖ < ∞`」として定義されている。

したがって教科書的な「絶対可積分性（measurable + ∫|f|<∞）」と同値という主張は
定義の言い換え（`Iff.rfl` レベル）として整理できる。

ここでは「ノート用に定義を再掲」する。
-/

section AbsoluteIntegrability

variable {α : Type*} [MeasurableSpace α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure α}

/-- ノート側の「絶対可積分性」：a.e.強可測 + HasFiniteIntegral（= ∫ ‖f‖ < ∞）。 -/
def AbsIntegrable (f : α → E) (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

/-- `Integrable` はまさに `AEStronglyMeasurable ∧ HasFiniteIntegral`。-/
theorem integrable_iff_aestronglyMeasurable_and_hasFiniteIntegral (f : α → E) :
    Integrable f μ ↔ AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ := by
  rfl

/-- ノート定義 `AbsIntegrable` と Mathlib の `Integrable` は定義的に同じ。 -/
theorem absIntegrable_iff_integrable (f : α → E) :
    AbsIntegrable (μ := μ) f ↔ Integrable f μ := by
  rfl

end AbsoluteIntegrability


/-!
## 3. 積測度（product measure）

Mathlibの積測度は `μ.prod ν : Measure (α × β)`。

基本性質：
- （可測集合 `s` について）定義：`(μ.prod ν) s = ∫⁻ x, ν {y | (x,y)∈s} ∂μ`
- 矩形集合について：`(μ.prod ν) (s ×ˢ t) = μ s * ν t`
-/

section ProductMeasure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β)

@[simp] theorem prod_apply {s : Set (α × β)} [SFinite ν] (hs : MeasurableSet s) :
    (μ.prod ν) s = ∫⁻ x : α, ν (Prod.mk x ⁻¹' s) ∂μ := by
  -- Mathlib: `Measure.prod_apply`
  simpa using (MeasureTheory.Measure.prod_apply (μ := μ) (ν := ν) hs)

@[simp] theorem prod_prod (s : Set α) (t : Set β) [SFinite ν] :
    (μ.prod ν) (s ×ˢ t) = μ s * ν t := by
  -- Mathlib: `Measure.prod_prod`
  simpa using (MeasureTheory.Measure.prod_prod (μ := μ) (ν := ν) s t)

end ProductMeasure


/-!
## 4. Tonelli–Fubini（積測度での反復積分）

- Tonelli：`ℝ≥0∞` 値（下側ルベーグ積分 `∫⁻`）
- Fubini：Bochner積分（`∫`）で `Integrable` を仮定

（※ `lintegral_prod_of_measurable` は deprecated なので使わない）
-/

section FubiniTonelli

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [SFinite μ] [SFinite ν]

/-- **Tonelli**（`ℝ≥0∞` 値，a.e. 可測で十分）。 -/
theorem tonelli_lintegral
    (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    (∫⁻ z, f z ∂(μ.prod ν)) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  -- Mathlib: `MeasureTheory.lintegral_prod`
  simpa using (MeasureTheory.lintegral_prod (μ := μ) (ν := ν) f hf)

/-- Tonelli の順序入替版（右辺を `y`→`x` の順にした形）。 -/
theorem tonelli_lintegral_symm
    (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    (∫⁻ z, f z ∂(μ.prod ν)) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  -- Mathlib: `MeasureTheory.lintegral_prod_symm`
  simpa using (MeasureTheory.lintegral_prod_symm (μ := μ) (ν := ν) f hf)

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **Fubini**（Bochner積分）：`Integrable f (μ.prod ν)` を仮定して反復積分に落とす。 -/
theorem fubini_integral
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    (∫ z, f z ∂(μ.prod ν)) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  -- Mathlib: `MeasureTheory.integral_prod`
  simpa using (MeasureTheory.integral_prod (μ := μ) (ν := ν) hf)

/-- Fubini の「内側を先に積分した関数」が可積分であること。 -/
theorem integrable_integral_section_right
    (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x : α => ∫ y : β, f (x, y) ∂ν) μ := by
  -- Mathlib: `MeasureTheory.Integrable.integral_prod_right`
  simpa using (MeasureTheory.Integrable.integral_prod_right (μ := μ) (ν := ν) (f := f) hf)

/-- 「可積分性の判定」：Fubini–Tonelli系の `integrable_prod_iff`（標準形）。 -/
theorem integrable_prod_iff
    (f : α × β → E) :
    Integrable f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, Integrable (fun y : β => f (x, y)) ν) ∧
      Integrable (fun x : α => ∫ y : β, ‖f (x, y)‖ ∂ν) μ := by
  -- Mathlib: `MeasureTheory.integrable_prod_iff`
  simpa using (MeasureTheory.integrable_prod_iff (μ := μ) (ν := ν) (f := f))

end FubiniTonelli


/-!
## 5. 収束定理の応用：積分記号下での微分（differentiation under the integral）

Mathlib: `Mathlib.Analysis.Calculus.ParametricIntegral` に既に一般形がある。

ここでは講義ノート用に「再掲・再命名」しておく：
`hasFDerivAt_integral_of_dominated_loc_of_lip`（局所 Lipschitz + 優関数で支配）
-/

section DifferentiateUnderIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- （ノート版）**積分記号下での微分**（Fréchet微分）：
`x ↦ ∫ a, F x a ∂μ` の微分を `∫ a, F' a ∂μ` として与える。 -/
theorem hasFDerivAt_integral_under_dominated_loc_of_lip
    {F : H → α → E} {x₀ : H} {bound : α → ℝ} {ε : ℝ}
    {F' : α → H →L[ℝ] E}
    (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in nhds x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs (bound a)) (fun x : H => F x a) (Metric.ball x₀ ε))
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (fun x : H => F x a) (F' a) x₀) :
    Integrable F' μ ∧
      HasFDerivAt (fun x : H => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  -- Mathlib の定理そのものに `simpa` で落とす
  simpa using
    (hasFDerivAt_integral_of_dominated_loc_of_lip
      (μ := μ) (F := F) (x₀ := x₀) (bound := bound) (ε := ε) (F' := F')
      ε_pos hF_meas hF_int hF'_meas h_lip bound_integrable h_diff)

end DifferentiateUnderIntegral

end LebesgueLecture
