import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Lebesgue積分論（講義ノート / Lean）: 応用編

このファイルでは，既に形式化した Lebesgue 積分論（単関数 → 非負 → 符号付き）に続いて，
収束定理の応用と積測度を扱う．

主な内容：

* 支配収束による **パラメータ付き積分の連続性**
* **積分記号下での微分**（differentiation under the integral sign）
* **測度の完備化**（`NullMeasurableSpace` と `Measure.completion`）
* **可積分性と絶対可積分性**（`Integrable` は「絶対可積分」を表現している）
* **積測度** と **Fubini–Tonelli**
* （おまけ）σ-finite を仮定しない compact support 版 Fubini
* （おまけ）変数変換公式（Jacobian）

Mathlib の既存定義・定理を参照しつつ，講義ノートとして読みやすいラッパーを用意する方針．
-/

open scoped BigOperators Topology
open Filter
open MeasureTheory

namespace LebesgueNotes

section ParametricIntegral

variable {α : Type*} {β : Type*} {E : Type*}
variable [TopologicalSpace α] [FirstCountableTopology α]
variable [MeasurableSpace β] {μ : Measure β}
variable [NormedAddCommGroup E] [CompleteSpace E]

/-!
## パラメータ付き積分の連続性

`MeasureTheory.continuous_of_dominated` など（Bochner 積分版の支配収束系の補題）を
講義ノート用にそのまま使える形で再輸出する．

注意：ここでの積分 `∫ a, F x a ∂μ` は Bochner 積分．
-/

/-- 支配収束（優収束）の形の仮定から，`x ↦ ∫ a, F x a` が連続になる． -/
theorem continuous_integral_of_dominated
    {F : α → β → E} {bound : β → ℝ}
    (hF_meas : ∀ x : α, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x : α, ∀ᵐ a : β ∂μ, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a : β ∂μ, Continuous fun x : α => F x a) :
    Continuous (fun x : α => ∫ a : β, F x a ∂μ) := by
  simpa using
    (MeasureTheory.continuous_of_dominated
      (μ := μ) (F := F) (bound := bound)
      hF_meas h_bound bound_integrable h_cont)

/-- `x₀` での連続性版． -/
theorem continuousAt_integral_of_dominated
    {F : α → β → E} {bound : β → ℝ} {x₀ : α}
    (hF_meas : ∀ x : α, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x : α, ∀ᵐ a : β ∂μ, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a : β ∂μ, ContinuousAt (fun x : α => F x a) x₀) :
    ContinuousAt (fun x : α => ∫ a : β, F x a ∂μ) x₀ := by
  simpa using
    (MeasureTheory.continuousAt_of_dominated
      (μ := μ) (F := F) (bound := bound) (x₀ := x₀)
      hF_meas h_bound bound_integrable h_cont)

end ParametricIntegral

section DifferentiateUnderIntegral

/-!
## 積分記号下での微分

`Mathlib.Analysis.Calculus.ParametricIntegral` の
`hasDerivAt_integral_of_dominated_loc_of_lip` を用いる．

定式化の要点（直感）：

* 近傍での a.e. 可測性（Bochner 積分が定義できるように）
* `F x₀` の可積分性
* 各 `a` について `x ↦ F x a` が（局所一様に）Lipschitz
* 各 `a` について `x₀` で微分可能で導関数 `F' a` を持つ

結論：

`x ↦ ∫ a, F x a ∂μ` は `x₀` で微分可能で，導関数は `∫ a, F' a ∂μ`.
-/

variable {β : Type*} [MeasurableSpace β] {μ : Measure β}
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- `hasDerivAt_integral_of_dominated_loc_of_lip` の講義ノート向けの薄い wrapper． -/
theorem hasDerivAt_integral_of_dominated_loc_of_lip'
    {bound : β → ℝ} {ε : ℝ} {F : 𝕜 → β → E} {x₀ : 𝕜} {F' : β → E}
    (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x : 𝕜 in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a : β ∂μ,
      LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 => F x a) (Metric.ball x₀ ε))
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a : β ∂μ, HasDerivAt (fun x : 𝕜 => F x a) (F' a) x₀) :
    Integrable F' μ ∧
      HasDerivAt (fun x : 𝕜 => ∫ a : β, F x a ∂μ) (∫ a : β, F' a ∂μ) x₀ := by
  simpa using
    (hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := μ) (F := F) (F' := F') (bound := bound) (x₀ := x₀) (ε := ε)
      ε_pos hF_meas hF_int hF'_meas h_lipsch bound_integrable h_diff)

/-- 上の補題から `deriv` の等式を取り出す（`𝕜 = ℝ` or `𝕜 = ℂ`）． -/
theorem deriv_integral_of_dominated_loc_of_lip
    {bound : β → ℝ} {ε : ℝ} {F : 𝕜 → β → E} {x₀ : 𝕜} {F' : β → E}
    (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x : 𝕜 in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a : β ∂μ,
      LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 => F x a) (Metric.ball x₀ ε))
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a : β ∂μ, HasDerivAt (fun x : 𝕜 => F x a) (F' a) x₀) :
    deriv (fun x : 𝕜 => ∫ a : β, F x a ∂μ) x₀ = (∫ a : β, F' a ∂μ) := by
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip'
      (μ := μ) (bound := bound) (ε := ε) (F := F) (x₀ := x₀) (F' := F')
      ε_pos hF_meas hF_int hF'_meas h_lipsch bound_integrable h_diff).2
  simpa using h.deriv

end DifferentiateUnderIntegral

section Completion

/-!
## 測度の完備化

`NullMeasurableSpace α μ` 上の測度 `μ.completion` を用いる．
これは「`μ`-null measurable 集合全体」に対する最小の完備化に相当する．

Mathlib では `μ.completion` が常に complete（`IsComplete`）になるインスタンスがある．
-/

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)

/-- 完備化した測度（型は `NullMeasurableSpace α μ` 上の測度）． -/
abbrev μᶜ : Measure (NullMeasurableSpace α μ) := μ.completion

/-- `μᶜ` は完備（complete）である． -/
instance : (μᶜ μ).IsComplete := by
  dsimp [μᶜ]
  infer_instance

@[simp] theorem completion_apply (s : Set α) : (μᶜ μ) s = μ s := by
  simpa [μᶜ] using (Measure.completion_apply (μ := μ) s)

@[simp] theorem coe_completion : (fun s : Set α => (μᶜ μ) s) = fun s => μ s := by
  -- `⇑μ.completion = ⇑μ`
  simpa [μᶜ] using (Measure.coe_completion (μ := μ))

end Completion

section IntegrableVsAbsolute

/-!
## 可積分性と絶対可積分性

Mathlib の `Integrable f μ` は（Bochner 積分としての）
「`f` が a.e. 強可測で `∫ ‖f‖ < ∞`」を意味する．

特に `E = ℝ` なら `‖f‖ = |f|` なので，これは古典的な意味での
「絶対可積分（`∫ |f| < ∞`）」を表す．

ここでは，講義ノートとして

* `Integrable f μ` から `Integrable (fun x => ‖f x‖) μ`
* 実数値の場合 `Integrable f μ ↔ Integrable (fun x => |f x|) μ`

を再輸出する．
-/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {E : Type*} [NormedAddCommGroup E]

/-- `f` が可積分なら `‖f‖` も可積分． -/
theorem Integrable.norm' {f : α → E} (hf : Integrable f μ) : Integrable (fun x => ‖f x‖) μ :=
  hf.norm

/-- 実数値関数の場合：可積分性は絶対可積分性と同値（ただし可測性は `Integrable` 側に含まれる）． -/
theorem integrable_iff_integrable_abs
    {f : α → ℝ} (hf_meas : AEStronglyMeasurable f μ) :
    Integrable f μ ↔ Integrable (fun x => |f x|) μ := by
  constructor
  · intro hf
    simpa using hf.abs
  · intro habs
    -- `Integrable` の定義は `AEStronglyMeasurable ∧ HasFiniteIntegral`．
    -- `|f|` が可積分なら `HasFiniteIntegral |f|` が得られるので，
    -- `‖f‖ = |f|` を使って `HasFiniteIntegral f` に落とす．
    refine ⟨hf_meas, ?_⟩
    have hfi : HasFiniteIntegral (fun x => |f x|) μ := habs.hasFiniteIntegral
    -- `HasFiniteIntegral` は `∫⁻ x, ‖·‖ₑ < ∞` なので，
    -- 右辺の integrand を `simp` で `f` のものに揃える．
    -- ここで `‖f x‖ = |f x|`（`Real.norm_eq_abs`）と `abs_abs` を使う．
    simpa [HasFiniteIntegral, Real.norm_eq_abs] using hfi

end IntegrableVsAbsolute

section ProdMeasure

/-!
## 積測度と Fubini–Tonelli

* Tonelli: 非負可測関数について `lintegral` を反復してよい
* Fubini: Bochner 可積分関数について `integral` を反復してよい

Mathlib では `μ.prod ν` が積測度で，`MeasureTheory.lintegral_prod`，
`MeasureTheory.integral_prod`，`MeasureTheory.integral_integral_swap` などを使う．
-/

variable {α : Type*} {β : Type*} {E : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [SigmaFinite μ] [SigmaFinite ν]

/-!
### Tonelli（`lintegral` 版）
-/

/-- Tonelli（`lintegral`）: `f ≥ 0` 可測なら反復 `lintegral` が積測度の `lintegral` に一致． -/
theorem lintegral_prod_tonelli
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂(μ.prod ν)) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  -- `lintegral_prod` は Tonelli の定理
  simpa using (MeasureTheory.lintegral_prod (μ := μ) (ν := ν) hf)

/-!
### Fubini（Bochner 積分版）
-/

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]

/-- Fubini: curried 形（`f : α → β → E`）の反復積分． -/
theorem integral_integral_eq_integral_prod
    {f : α → β → E}
    (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) = ∫ z, f z.1 z.2 ∂(μ.prod ν) := by
  simpa using (MeasureTheory.integral_integral (μ := μ) (ν := ν) hf)

/-- Fubini（対称版）: `∫∫ = ∫` を swap した形． -/
theorem integral_integral_swap
    {f : α × β → E}
    (hf : Integrable f (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  simpa using (MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) hf)

/-!
### σ-finite を仮定しない compact support 版

局所有限（`IsLocallyFiniteMeasure`）かつ連続かつ compact support なら Fubini が成立する．
-/

section CompactSupportFubini

variable [TopologicalSpace α] [TopologicalSpace β]
variable [LocallyCompactSpace α] [LocallyCompactSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]

/-- σ-finite を仮定しない（連続 + compact support）版の Fubini． -/
theorem integral_integral_swap_of_hasCompactSupport
    {f : α × β → E}
    (hf_cont : Continuous f) (hf_supp : HasCompactSupport f) :
    (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  simpa using
    (MeasureTheory.integral_integral_swap_of_hasCompactSupport
      (μ := μ) (ν := ν) (f := f) hf_cont hf_supp)

end CompactSupportFubini

end ProdMeasure

section ChangeOfVariables

/-!
## （おまけ）変数変換（Jacobian）

`Mathlib.MeasureTheory.Function.Jacobian` の変数変換公式を再輸出する．

ここでは典型的な形の定理（`integral_image_eq_integral_abs_det_fderiv_smul`）のみ記す．
詳細な仮定（可微分性，局所可逆性，測度零集合の扱いなど）は Mathlib に委ねる．
-/

/-!
このトピックは仮定がやや長くなりがちなので，講義ノート側では
Mathlib の定理をそのまま「再輸出」するに留める．

代表例（Jacobian 公式）:

* `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`
* `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`

（必要に応じて `#check` で仮定・結論を確認して使うこと．）
-/

theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul :=
  MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul

theorem integral_image_eq_integral_abs_det_fderiv_smul :=
  MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul

end ChangeOfVariables

end LebesgueNotes
