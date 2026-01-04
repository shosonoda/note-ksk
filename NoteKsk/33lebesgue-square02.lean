/-
Lebesgue 積分論ノート（続き）：
  * L² の内積 = 積分
  * Bessel 不等式（直交正規族）
  * Hilbert 基底（HilbertBasis）の存在と Fourier 展開（HasSum）
  * Parseval 恒等式（内積版）
  * 直交射影の基本性質（直交性・Pythagoras 型分解）
  * L² 版 Parseval（積分表示）
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators
noncomputable section

namespace Lebesgue

/-- `L²` の内積は点ごとの内積の積分で定義される。 -/
section L2Inner

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open MeasureTheory

-- `α →₂[μ] E` を「`Lp E 2 μ` の台の型」として扱う（Mathlib 側の実装に合わせる）
local notation3:25 α " →₂[" μ "] " E => ↥(MeasureTheory.Lp E 2 μ)

/-- `L²` の内積は `∫ ⟪f(x), g(x)⟫ dμ`。 -/
theorem L2_inner_def (f g : α →₂[μ] E) :
    inner f g = ∫ a : α, inner (↑↑f a) (↑↑g a) ∂μ := by
  simpa using (MeasureTheory.L2.inner_def (μ := μ) f g)

/-- `f,g ∈ L²` なら `x ↦ ⟪f x, g x⟫` は可積分。 -/
theorem L2_integrable_inner (f g : α →₂[μ] E) :
    MeasureTheory.Integrable (fun a : α => inner (↑↑f a) (↑↑g a)) μ := by
  simpa using (MeasureTheory.L2.integrable_inner (μ := μ) f g)

end L2Inner


/-- 一般 Hilbert 空間の基本：Bessel / HilbertBasis 展開 / Parseval（内積版）。 -/
section HilbertTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Bessel 不等式（直交正規族） -/

/-- Bessel 不等式：`∑ ‖⟪v i, x⟫‖² ≤ ‖x‖²`（tsum 版）。 -/
theorem Orthonormal.bessel {ι : Type*} {v : ι → H} (hv : Orthonormal v) (x : H) :
    (∑' i : ι, ‖inner (v i) x‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  simpa using hv.tsum_inner_products_le x

/-- Bessel から従う：`i ↦ ‖⟪v i, x⟫‖²` は `Summable`。 -/
theorem Orthonormal.summable_norm_inner_sq {ι : Type*} {v : ι → H}
    (hv : Orthonormal v) (x : H) :
    Summable (fun i : ι => ‖inner (v i) x‖ ^ 2) := by
  simpa using hv.inner_products_summable x


/-! ### Hilbert 基底（HilbertBasis）と Fourier 展開 -/

variable [CompleteSpace H]

/-- Hilbert 空間は Hilbert 基底（`HilbertBasis`）を持つ（存在のみ）。 -/
theorem exists_hilbertBasis_set :
    ∃ (w : Set H) (b : HilbertBasis (↑w) 𝕜 H), (⇑b = Subtype.val) := by
  simpa using (exists_hilbertBasis (𝕜 := 𝕜) H)

namespace HilbertBasis

variable {ι : Type*} (b : HilbertBasis ι 𝕜 H)

/-- Hilbert 基底は直交正規族である。 -/
theorem orthonormal : Orthonormal (fun i : ι => b i) := by
  simpa using (b.orthonormal)

/-- Hilbert 基底の線形包は稠密（閉包が全体）。 -/
theorem dense_span :
    (Submodule.span 𝕜 (Set.range (fun i : ι => b i))).topologicalClosure = ⊤ := by
  -- `HilbertBasis.dense_span` は `[simp]` になっている
  simpa using (b.dense_span)

/-- 座標表示 `b.repr` の各座標は内積で与えられる：`(b.repr x)i = ⟪b i, x⟫`。 -/
theorem repr_apply (x : H) (i : ι) :
    (↑(b.repr x) i : 𝕜) = inner (b i) x := by
  simpa using (b.repr_apply_apply x i)

/-- Fourier 展開（抽象）：
`x = ∑ (⟪b i, x⟫) • b i` が `HasSum` として成り立つ。 -/
theorem hasSum_fourier (x : H) :
    HasSum (fun i : ι => (inner (b i) x) • (b i)) x := by
  -- `b.hasSum_repr x : HasSum (fun i => ↑(b.repr x) i • b i) x`
  -- `repr_apply_apply` で係数を書き換える
  simpa [b.repr_apply_apply] using (b.hasSum_repr x)

/-- Parseval 恒等式（内積版）：
`⟪x,y⟫ = ∑ ⟪x,b i⟫ * ⟪b i,y⟫`。 -/
theorem tsum_inner_mul_inner (x y : H) :
    (∑' i : ι, inner x (b i) * inner (b i) y) = inner x y := by
  simpa using (b.tsum_inner_mul_inner x y)

end HilbertBasis

end HilbertTheory


/-- 直交射影（orthogonalProjection）の基本：直交性と Pythagoras 型分解。 -/
section OrthogonalProjection

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {U : Submodule 𝕜 H} [CompleteSpace ↥U]

/-- `x - proj_U x` は `Uᗮ` に属する。 -/
theorem sub_orthogonalProjection_mem_orthogonal (x : H) :
    x - (U.orthogonalProjection x : H) ∈ Uᗮ := by
  simpa using (U.sub_orthogonalProjection_mem_orthogonal x)

/-- Pythagoras 型の分解：
`‖x‖² = ‖proj_U x‖² + ‖x - proj_U x‖²`。 -/
theorem norm_sq_eq_add_norm_sq_projection (x : H) :
    ‖x‖ ^ 2 = ‖U.orthogonalProjection x‖ ^ 2 + ‖x - (U.orthogonalProjection x : H)‖ ^ 2 := by
  simpa using (U.norm_sq_eq_add_norm_sq_projection x)

end OrthogonalProjection


/-- `L²` に戻って：Parseval（内積版）と「積分表示」を結合する。 -/
section L2ParsevalAsIntegral

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]

open MeasureTheory

local notation3:25 α " →₂[" μ "] " 𝕜 => ↥(MeasureTheory.Lp 𝕜 2 μ)

/-- `L²` は Hilbert 空間なので Hilbert 基底が存在する（存在のみ）。 -/
theorem exists_hilbertBasis_L2 :
    ∃ (w : Set (α →₂[μ] 𝕜)) (b : HilbertBasis (↑w) 𝕜 (α →₂[μ] 𝕜)), (⇑b = Subtype.val) := by
  simpa using (exists_hilbertBasis (𝕜 := 𝕜) (E := (α →₂[μ] 𝕜)))

/--
`L²` 版 Parseval（積分表示）：

`∑' i, ⟪f, b i⟫ * ⟪b i, g⟫ = ∫ ⟪f(x), g(x)⟫ dμ` 。

（左辺 = `inner f g` は `HilbertBasis.tsum_inner_mul_inner`、
 右辺 = `inner f g` は `MeasureTheory.L2.inner_def`。）
-/
theorem L2_parseval_integral {ι : Type*}
    (b : HilbertBasis ι 𝕜 (α →₂[μ] 𝕜)) (f g : α →₂[μ] 𝕜) :
    (∑' i : ι, inner f (b i) * inner (b i) g)
      = ∫ a : α, inner (↑↑f a) (↑↑g a) ∂μ := by
  calc
    (∑' i : ι, inner f (b i) * inner (b i) g) = inner f g := by
      simpa using (b.tsum_inner_mul_inner f g)
    _ = ∫ a : α, inner (↑↑f a) (↑↑g a) ∂μ := by
      simpa using (MeasureTheory.L2.inner_def (μ := μ) f g)

end L2ParsevalAsIntegral

end Lebesgue
