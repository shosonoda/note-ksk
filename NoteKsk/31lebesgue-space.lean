/-
  Lebesgue 空間論（関数空間論）への導入：ノルム空間・Banach 空間と L¹ の完備性

  方針：
  * ノルム空間／Banach 空間は Mathlib の型クラス（`NormedAddCommGroup`, `NormedSpace`, `CompleteSpace`）をそのまま採用する
  * Minkowski 不等式（Lᵖ ノルムの三角不等式）は Mathlib の既存定理を参照して再定式化する
  * 可積分関数（a.e. 同値類としての `L¹`）が Banach 空間であることは Mathlib の instance を利用して確認する

  参考（Mathlib の流れ）：
  * `Mathlib/MeasureTheory/Function/LpSpace`：`Lp` 空間、`L¹` の記法、`snorm`、完備性など

  注意：
  * Tao の記法の「可積分関数全体」は通常「a.e. 同値類を取った L¹ 空間」を指すので、
    Lean/Mathlib でも `α →₁[μ] E`（= `Lp E 1 μ`）を主役にします。
-/

import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.NormedSpace.Basic

open scoped ENNReal
open MeasureTheory

namespace LebesgueSpaceNotes

/-!
## 1. ノルム空間と Banach 空間（Mathlib の定義）
-/

section NormedAndBanach

variable (𝕜 : Type*) [NormedField 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Banach 空間**：Mathlib では「ノルム（加法）群が完備である」ことを `CompleteSpace` で表す。 -/
abbrev IsBanachSpace (E : Type*) [NormedAddCommGroup E] : Prop :=
  CompleteSpace E

/-
  具体例（`infer_instance` で既存のインスタンスが入っていることを確認）：
  * `ℝ`, `ℂ` は Banach 空間
  * 直積も Banach
-/

example : NormedAddCommGroup ℝ := infer_instance
example : NormedSpace ℝ ℝ := infer_instance
example : CompleteSpace ℝ := infer_instance

example : NormedAddCommGroup ℂ := infer_instance
example : NormedSpace ℂ ℂ := infer_instance
example : CompleteSpace ℂ := infer_instance

example : NormedSpace ℝ (ℝ × ℝ) := infer_instance
example : CompleteSpace (ℝ × ℝ) := infer_instance

/-
  「Banach 空間である」という言い方をこのファイルでは `CompleteSpace` と同一視して扱う：
-/
example : IsBanachSpace (E := ℝ) ℝ := by
  -- `IsBanachSpace` は `CompleteSpace` の abbrev なので、既存 instance で解ける
  infer_instance

end NormedAndBanach

/-!
## 2. Minkowski 不等式（Lᵖ ノルムの三角不等式）

ここでは「`snorm` レベルの Minkowski」と「`Lp`（特に L¹）レベルの Minkowski（=三角不等式）」を
Mathlib の定理を参照して書き直します。
-/

section Minkowski

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E]

/--
`snorm`（= Lᵖ-準ノルム）についての Minkowski 不等式。

Mathlib では `MeasureTheory.snorm_add_le` がこれに相当する（`1 ≤ p` を `Fact` で渡す流儀）。
-/
theorem minkowski_snorm (p : ℝ≥0∞) (hp : 1 ≤ p) (f g : α → E) :
    snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ := by
  classical
  haveI : Fact (1 ≤ p) := ⟨hp⟩
  -- `snorm_add_le` は関数の点wise加法に対する Lᵖ 三角不等式
  simpa using (MeasureTheory.snorm_add_le (f := f) (g := g) (p := p) (μ := μ))

/--
`Lp` 空間上の Minkowski（= ノルムの三角不等式）。

`Lp E p μ` がノルム空間になるのは（少なくとも）`1 ≤ p` を仮定する場面が中心。
そのとき `norm_add_le` が Minkowski そのもの。
-/
theorem minkowski_Lp
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f g : MeasureTheory.Lp E p μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  simpa using (norm_add_le f g)

/--
特に L¹（Tao の意味での「可積分関数の a.e. 同値類」）では Minkowski は単なる三角不等式。
-/
theorem minkowski_L1 (f g : (α →₁[μ] E)) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  simpa using (norm_add_le f g)

end Minkowski

/-!
## 3. L¹（可積分関数の空間）は Banach 空間

結論：
`E` が Banach（=完備）なら、`L¹(μ;E)`（Lean では `α →₁[μ] E`）も Banach。

Mathlib では `Lp` 空間の完備性が instance として用意されているので、
`infer_instance` で完備性（`CompleteSpace`）が得られます。
-/

section L1IsBanach

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- `L¹(μ;E)` は（`E` がノルム空間なら）ノルム空間になる。-/
example : NormedSpace 𝕜 (α →₁[μ] E) := by
  infer_instance

/-- `L¹(μ;E)` は（`E` が完備なら）完備：すなわち Banach 空間。-/
theorem L1_completeSpace : CompleteSpace (α →₁[μ] E) := by
  infer_instance

/-- まとめ：`L¹(μ;E)` は Banach 空間（このファイルの `IsBanachSpace` による言い換え）。-/
theorem L1_isBanach : IsBanachSpace (E := (α →₁[μ] E)) (α →₁[μ] E) := by
  -- `IsBanachSpace` = `CompleteSpace`
  infer_instance

/-
  ついでに（講義ノート向け）：
  `Lp` 全体でも `1 ≤ p` を仮定すれば同様に Banach（`E` が Banach のとき）。
-/
theorem Lp_completeSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (MeasureTheory.Lp E p μ) := by
  infer_instance

end L1IsBanach

end LebesgueSpaceNotes
