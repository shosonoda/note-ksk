import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Lebesgue積分論（導入）

このファイルは講義ノート用の「定義の再提示」ファイルである．
Mathlib で既に定義済みの概念を `abbrev` として再導入し，
blueprint から参照しやすい名前・形で定理を並べる．

参照：
* `Mathlib.MeasureTheory.Function.SimpleFunc`
* `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`（`lintegral` と `lintegral_def` など）
* `Mathlib.MeasureTheory.Integral.Bochner.Basic`（実数値積分の性質）
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace LebesgueLecture

/-! ## 1. 可測性 -/

section Measurability

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- 集合 `s` が可測であること（`MeasurableSet s` の別名）． -/
abbrev IsMeasurableSet (s : Set α) : Prop := MeasurableSet s

/-- 関数 `f` が可測であること（`Measurable f` の別名）． -/
abbrev IsMeasurable (f : α → β) : Prop := Measurable f

/-- `μ` に関して a.e. 可測（`AEMeasurable f μ` の別名）． -/
abbrev IsAEMeasurable (μ : Measure α) (f : α → β) : Prop := AEMeasurable f μ

/-- `μ` に関して a.e. 強可測（`AEStronglyMeasurable f μ` の別名）． -/
abbrev IsAEStronglyMeasurable (μ : Measure α) (f : α → β) : Prop := AEStronglyMeasurable f μ

-- ### 可測集合：基本例と閉性

theorem isMeasurableSet_univ : IsMeasurableSet (Set.univ : Set α) := by
  simpa [IsMeasurableSet] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set α))

theorem isMeasurableSet_empty : IsMeasurableSet (∅ : Set α) := by
  simpa [IsMeasurableSet] using (MeasurableSet.empty : MeasurableSet (∅ : Set α))

theorem isMeasurableSet_compl {s : Set α} (hs : IsMeasurableSet s) : IsMeasurableSet sᶜ := by
  simpa [IsMeasurableSet] using (show MeasurableSet s from hs).compl

theorem isMeasurableSet_iUnion {ι : Type*} [Countable ι] {s : ι → Set α}
    (hs : ∀ i, IsMeasurableSet (s i)) : IsMeasurableSet (⋃ i, s i) := by
  simpa [IsMeasurableSet] using
    (MeasurableSet.iUnion fun i => (show MeasurableSet (s i) from hs i))

theorem isMeasurableSet_iInter {ι : Type*} [Countable ι] {s : ι → Set α}
    (hs : ∀ i, IsMeasurableSet (s i)) : IsMeasurableSet (⋂ i, s i) := by
  simpa [IsMeasurableSet] using
    (MeasurableSet.iInter fun i => (show MeasurableSet (s i) from hs i))

-- ### 可測関数：基本例と閉性

theorem isMeasurable_const (c : β) : IsMeasurable (fun _ : α => c) := by
  simpa [IsMeasurable] using (measurable_const : Measurable (fun _ : α => c))

theorem isMeasurable_id : IsMeasurable (fun x : α => x) := by
  simpa [IsMeasurable] using (measurable_id : Measurable (fun x : α => x))

theorem isMeasurable_comp {f : α → β} {g : β → γ}
    (hg : IsMeasurable g) (hf : IsMeasurable f) : IsMeasurable (g ∘ f) := by
  simpa [IsMeasurable, Function.comp] using
    (show Measurable g from hg).comp (show Measurable f from hf)

section Indicator

variable [Zero β]

/-- 可測集合 `s` と可測関数 `f` から得られる indicator `s.indicator f` も可測． -/
theorem isMeasurable_indicator {s : Set α} (hs : IsMeasurableSet s) {f : α → β}
    (hf : IsMeasurable f) : IsMeasurable (s.indicator f) := by
  have hs' : MeasurableSet s := by simpa [IsMeasurableSet] using hs
  have hf' : Measurable f := by simpa [IsMeasurable] using hf
  simpa [IsMeasurable] using hf'.indicator hs'

end Indicator

section Arithmetic

/-!
`ℝ` などの標準的な型では加算・乗算は Borel 可測なので，
可測関数は和や積で閉じる．
-/

variable {f g : α → ℝ}

theorem isMeasurable_add (hf : IsMeasurable f) (hg : IsMeasurable g) :
    IsMeasurable fun x => f x + g x := by
  have hf' : Measurable f := by simpa [IsMeasurable] using hf
  have hg' : Measurable g := by simpa [IsMeasurable] using hg
  simpa [IsMeasurable] using hf'.add hg'

theorem isMeasurable_mul (hf : IsMeasurable f) (hg : IsMeasurable g) :
    IsMeasurable fun x => f x * g x := by
  have hf' : Measurable f := by simpa [IsMeasurable] using hf
  have hg' : Measurable g := by simpa [IsMeasurable] using hg
  simpa [IsMeasurable] using hf'.mul hg'

theorem isMeasurable_neg (hf : IsMeasurable f) :
    IsMeasurable fun x => -f x := by
  have hf' : Measurable f := by simpa [IsMeasurable] using hf
  simpa [IsMeasurable] using hf'.neg

theorem isMeasurable_sub (hf : IsMeasurable f) (hg : IsMeasurable g) :
    IsMeasurable fun x => f x - g x := by
  have hf' : Measurable f := by simpa [IsMeasurable] using hf
  have hg' : Measurable g := by simpa [IsMeasurable] using hg
  simpa [IsMeasurable] using hf'.sub hg'

end Arithmetic

-- ### 単関数は可測（`SimpleFunc.measurable`）

theorem simpleFunc_isMeasurable (f : MeasureTheory.SimpleFunc α β) :
    IsMeasurable (fun x => f x) := by
  simpa [IsMeasurable] using f.measurable

theorem simpleFunc_isAEMeasurable (μ : Measure α) (f : MeasureTheory.SimpleFunc α β) :
    IsAEMeasurable μ (fun x => f x) := by
  simpa [IsAEMeasurable] using f.aemeasurable

end Measurability

/-! ## 2. Lebesgue 積分（単関数→非負関数→符号付き関数） -/

section LebesgueIntegral

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)

-- ### 2.1 単関数の積分（`ℝ≥0∞` 値）

/-- `ℝ≥0∞` 値単関数（講義ノート用の別名）． -/
abbrev SimpleNNFun := MeasureTheory.SimpleFunc α ENNReal

/-- 単関数の（下）Lebesgue 積分：`SimpleFunc.lintegral` をそのまま使う． -/
noncomputable abbrev simpleLintegral (f : SimpleNNFun (α := α)) : ENNReal :=
  f.lintegral μ

-- ### 2.2 非負可測関数の積分（`ℝ≥0∞` 値）

/-- 非負（拡張）実数値関数の下 Lebesgue 積分：`MeasureTheory.lintegral` を別名で導入． -/
noncomputable abbrev lintegralNN (f : α → ENNReal) : ENNReal :=
  MeasureTheory.lintegral μ f

/-- `lintegral` は「`f` 以下の単関数の積分の上限」として定義される（`lintegral_def`）．  -/
theorem lintegralNN_def (f : α → ENNReal) :
    lintegralNN (μ := μ) f =
      ⨆ (g : SimpleNNFun (α := α)), ⨆ (_ : (g : α → ENNReal) ≤ f), g.lintegral μ := by
  simpa [lintegralNN] using (MeasureTheory.lintegral_def (μ := μ) (f := f))

/-- `lintegral` は単関数に一致する（`SimpleFunc.lintegral_eq_lintegral`）．  -/
theorem lintegralNN_eq_simple (f : SimpleNNFun (α := α)) :
    lintegralNN (μ := μ) (fun x => f x) = simpleLintegral (μ := μ) f := by
  simpa [lintegralNN, simpleLintegral] using
    (MeasureTheory.SimpleFunc.lintegral_eq_lintegral (f := f) (μ := μ))

-- ### 2.3 非負の実数値関数の積分（`toReal ∘ lintegral ∘ ofReal`）

/-- 非負の実数値関数 `f : α → ℝ` の積分は `ENNReal.ofReal` で `ℝ≥0∞` に移してから
`lintegral` を取り，`toReal` で戻す（`integral_eq_lintegral_of_nonneg_ae`）．  -/
theorem integral_eq_toReal_lintegral_ofReal
    {f : α → ℝ} (hf : 0 ≤ᶠ[μ.ae] f) (hfm : AEStronglyMeasurable f μ) :
    (∫ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  simpa using (MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := μ) (f := f) hf hfm)

-- ### 2.4 符号付き関数の積分（正負部分の差）

/-- 講義ノート用：実数値関数 `f` の「正部分」．
`ENNReal.ofReal` は負の値を 0 に潰すので，これが `f⁺` に相当する． -/
noncomputable abbrev posPart (f : α → ℝ) : α → ENNReal := fun x => ENNReal.ofReal (f x)

/-- 講義ノート用：実数値関数 `f` の「負部分」．
`(-f)⁺` に対応するので `ENNReal.ofReal (-f x)` と書く． -/
noncomputable abbrev negPart (f : α → ℝ) : α → ENNReal := fun x => ENNReal.ofReal (-f x)

/-- Bochner 積分 `∫ f` は正部分と負部分の `lintegral` の差（`integral_eq_lintegral_pos_part_sub_lintegral_neg_part`）．  -/
theorem integral_eq_posPart_sub_negPart
    {f : α → ℝ} (hfi : Integrable f μ) :
    (∫ x, f x ∂μ) =
      (∫⁻ x, posPart (α := α) f x ∂μ).toReal -
        (∫⁻ x, negPart (α := α) f x ∂μ).toReal := by
  simpa [posPart, negPart] using
    (MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part (μ := μ) (f := f) hfi)

/-- （講義ノートで）上の右辺を “定義” として採用する場合． -/
noncomputable def lebesgueIntegral (f : α → ℝ) (hfi : Integrable f μ) : ℝ :=
  (∫⁻ x, posPart (α := α) f x ∂μ).toReal -
    (∫⁻ x, negPart (α := α) f x ∂μ).toReal

theorem lebesgueIntegral_eq_integral {f : α → ℝ} (hfi : Integrable f μ) :
    lebesgueIntegral (μ := μ) f hfi = (∫ x, f x ∂μ) := by
  simpa [lebesgueIntegral] using (integral_eq_posPart_sub_negPart (μ := μ) (f := f) hfi).symm

end LebesgueIntegral

end LebesgueLecture
