/-
  Linear operator theory (entrance) for Lebesgue integration notes.

  方針:
  * 「線形作用素」= `E →ₗ[𝕜] F`（連続性は仮定しない）
  * 「有界線形作用素」= 典型的な解析的定義 `∃ M, ‖Tx‖ ≤ M‖x‖` を
    mathlib の `IsBoundedLinearMap` で表現する（= 連続性と同値）
  * 「連続線形作用素」= `E →L[𝕜] F`（bundled）
  * 「作用素ノルム」= `‖T‖`（`ContinuousLinearMap` のノルム）
  * 「作用素空間」= `E →L[𝕜] F` がノルム線形空間になる
  * 「線形双対空間」= `NormedSpace.Dual 𝕜 E`（= `E →L[𝕜] 𝕜`）

  微分作用素（非有界例）について:
  * 典型例（C¹([0,1]) を sup ノルムで見たときの微分）は、講義では重要だが、
    Lean で「C¹ のノルム空間構造」をどう置くか（sup ノルムのみ/グラフノルム等）
    によって形式化の準備が必要になるので、ここでは “位置づけ” のコメントに留める。
  * もし `C¹` 空間を（`ContinuousMap` / `ContDiffMap` などを使って）構成済なら、
    その上で `¬ IsBoundedLinearMap` を示す lemma を別ファイルで追加するのが自然。

-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section

open scoped Topology

namespace LebesgueNotes

/-!
## 1. 線形作用素（連続性を仮定しない）
-/

section LinearOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- 講義ノート上の「線形作用素」(boundedness/continuity は仮定しない) -/
abbrev LinearOperator (𝕜 : Type*) (E : Type*) (F : Type*) := E →ₗ[𝕜] F

/-- 講義ノート上の「有界線形作用素 (= 連続線形作用素)」 -/
abbrev BoundedLinearOperator (𝕜 : Type*) (E : Type*) (F : Type*) := E →L[𝕜] F

-- 具体例（線形作用素）
example : LinearOperator 𝕜 E E := LinearMap.id
example : LinearOperator 𝕜 E F := 0
example : LinearOperator 𝕜 (E × F) E := LinearMap.fst 𝕜 E F
example : LinearOperator 𝕜 (E × F) F := LinearMap.snd 𝕜 E F

-- 具体例（有界線形作用素＝連続線形作用素）
example : BoundedLinearOperator 𝕜 E E := ContinuousLinearMap.id 𝕜 E
example : BoundedLinearOperator 𝕜 E F := 0
example : BoundedLinearOperator 𝕜 (E × F) E := ContinuousLinearMap.fst 𝕜 E F
example : BoundedLinearOperator 𝕜 (E × F) F := ContinuousLinearMap.snd 𝕜 E F

end LinearOperators

/-!
## 2. 有界性の定義と基本性質

数学的定義:
`T : E →ₗ[𝕜] F` が有界 ⇔ `∃ M > 0, ∀ x, ‖T x‖ ≤ M ‖x‖`.

mathlib では「関数」`f : E → F` に対して `IsBoundedLinearMap 𝕜 f` を用意している。
線形写像 `T : E →ₗ[𝕜] F` も coercion により `E → F` と見なせるので、そのまま使う。

重要同値:
* 連続性と有界性は同値（ノルム空間上の線形写像）
* 原点での連続性 ⇔ 全体での連続性（線形性による）
* 有界性 ⇔ Lipschitz（ある定数で） も同様に得られる
-/

section Boundedness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- 線形写像 `T` の「有界性」(unbundled) を `IsBoundedLinearMap` で表現する。 -/
abbrev LinearMap.IsBounded (T : E →ₗ[𝕜] F) : Prop :=
  IsBoundedLinearMap 𝕜 T

/-- 線形写像 `T` は「有界」 iff 「連続」。 -/
theorem LinearMap.isBounded_iff_continuous (T : E →ₗ[𝕜] F) :
    T.IsBounded ↔ Continuous T := by
  -- mathlib: `IsLinearMap f ∧ Continuous f ↔ IsBoundedLinearMap f`
  have hlin : IsLinearMap 𝕜 (T : E → F) := by
    refine
      { map_add := by intro x y; simpa using T.map_add x y
        map_smul := by intro c x; simpa using T.map_smul c x }
  have h :=
    (IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap
      (𝕜 := 𝕜) (E := E) (F := F) (f := (T : E → F)))
  constructor
  · intro hB
    -- bounded -> (linear ∧ continuous) -> continuous
    exact (h.symm.mp hB).2
  · intro hcont
    -- (linear ∧ continuous) -> bounded
    exact h.mp ⟨hlin, hcont⟩

/-- 線形写像の連続性は「原点での連続性」と同値。 -/
theorem LinearMap.continuous_iff_continuousAt_zero (T : E →ₗ[𝕜] F) :
    Continuous T ↔ ContinuousAt T 0 := by
  constructor
  · intro h
    exact h.continuousAt
  · intro h0
    -- 線形性より、`x ↦ T(x - x0) + T(x0)` で局所化できる
    refine (continuous_iff_continuousAt).2 ?_
    intro x0
    have hT0 : ContinuousAt T (x0 - x0) := by
      simpa using h0
    have hsub : ContinuousAt (fun x : E => x - x0) x0 := by
      simpa using (continuousAt_id.sub continuousAt_const)
    have hshift : ContinuousAt (fun x : E => T (x - x0)) x0 :=
      hT0.comp x0 hsub
    have hconst : ContinuousAt (fun _ : E => T x0) x0 := continuousAt_const
    have hadd : ContinuousAt (fun x : E => T (x - x0) + T x0) x0 :=
      hshift.add hconst
    have hEq : (fun x : E => T (x - x0) + T x0) = (T : E → F) := by
      funext x
      -- `T (x - x0) + T x0 = T ((x - x0) + x0) = T x`
      have := (T.map_add (x - x0) x0).symm
      simpa [sub_add_cancel] using this
    simpa [hEq] using hadd

/-- 有界性も「原点での連続性」と同値（上の二つを合成）。 -/
theorem LinearMap.isBounded_iff_continuousAt_zero (T : E →ₗ[𝕜] F) :
    T.IsBounded ↔ ContinuousAt T 0 := by
  -- IsBounded <-> Continuous <-> ContinuousAt 0
  exact (T.isBounded_iff_continuous.trans T.continuous_iff_continuousAt_zero)

/-- 有界線形写像は Lipschitz（ある定数で）である。 -/
theorem LinearMap.isBounded_exists_lipschitz (T : E →ₗ[𝕜] F) (hB : T.IsBounded) :
    ∃ K : ℝ≥0, LipschitzWith K T := by
  -- `IsBoundedLinearMap.bound` から定数 M を取って Lipschitz を示す
  rcases hB.bound with ⟨M, hMpos, hM⟩
  let K : ℝ≥0 := ⟨M, le_of_lt hMpos⟩
  refine ⟨K, ?_⟩
  intro x y
  -- dist(Tx,Ty) = ‖Tx - Ty‖ = ‖T(x - y)‖ ≤ M‖x - y‖ = K * dist x y
  calc
    dist (T x) (T y)
        = ‖T x - T y‖ := by simpa [dist_eq_norm]
    _ = ‖T (x - y)‖ := by
        -- `T x - T y = T (x - y)`
        simpa using congrArg (fun z => ‖z‖) ((T.map_sub x y).symm)
    _ ≤ M * ‖x - y‖ := hM (x - y)
    _ = (K : ℝ) * dist x y := by
        simp [K, dist_eq_norm]

/-- 線形写像に関して、有界性は「ある定数で Lipschitz」と同値。 -/
theorem LinearMap.isBounded_iff_exists_lipschitz (T : E →ₗ[𝕜] F) :
    T.IsBounded ↔ ∃ K : ℝ≥0, LipschitzWith K T := by
  constructor
  · intro hB
    exact T.isBounded_exists_lipschitz hB
  · rintro ⟨K, hK⟩
    -- Lipschitz -> continuous -> bounded
    have hcont : Continuous T := hK.continuous
    exact (T.isBounded_iff_continuous).2 hcont

end Boundedness

/-!
## 3. 作用素ノルム・作用素空間

bundled な連続線形写像 `T : E →L[𝕜] F` には operator norm `‖T‖` が入り、
`‖T x‖ ≤ ‖T‖‖x‖` が成り立つ。

また `E →L[𝕜] F` 自体が（`F` がノルム空間なら）ノルム空間になる。
-/

section OperatorNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- 作用素ノルムによる基本評価 `‖T x‖ ≤ ‖T‖ ‖x‖`. -/
theorem ContinuousLinearMap.norm_apply_le (T : E →L[𝕜] F) (x : E) :
    ‖T x‖ ≤ ‖T‖ * ‖x‖ := by
  simpa using T.le_opNorm x

/-- 作用素ノルムによる距離評価 `dist (T x) (T y) ≤ ‖T‖ * dist x y`. -/
theorem ContinuousLinearMap.dist_le (T : E →L[𝕜] F) (x y : E) :
    dist (T x) (T y) ≤ ‖T‖ * dist x y := by
  simpa using T.dist_le_opNorm x y

/-- `‖T x - T y‖ ≤ ‖T‖ ‖x - y‖` 版。 -/
theorem ContinuousLinearMap.norm_sub_le (T : E →L[𝕜] F) (x y : E) :
    ‖T x - T y‖ ≤ ‖T‖ * ‖x - y‖ := by
  -- 上の距離版から `dist_eq_norm` で変形
  simpa [dist_eq_norm] using T.dist_le_opNorm x y

/-- 作用素空間 `E →L[𝕜] F` は `𝕜`-ノルム空間（インスタンス確認用）。 -/
example : NormedSpace 𝕜 (E →L[𝕜] F) := by infer_instance

end OperatorNorm

/-!
## 4. 線形双対空間

`NormedSpace.Dual 𝕜 E` は `E →L[𝕜] 𝕜` の略語（連続線形汎関数全体）。
-/

section DualSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- 双対空間（連続線形汎関数全体）-/
abbrev Dual := NormedSpace.Dual 𝕜 E

variable (f : Dual) (x : E)

/-- 双対元 `f` についても `‖f x‖ ≤ ‖f‖‖x‖`. -/
theorem dual_norm_apply_le : ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
  simpa using f.le_opNorm x

/-- 二重双対への包含 `E →L[𝕜] Dual 𝕜 (Dual 𝕜 E)` が用意されている。-/
#check NormedSpace.inclusionInDoubleDual 𝕜 E

end DualSpace

/-!
## 5. 非有界線形作用素（微分作用素）について（コメント）

解析の典型例:
* `E = C¹([0,1])` に「関数の sup ノルム」`‖f‖∞ := sup |f(x)|` を入れる
* `F = C([0,1])` に同様の sup ノルム
* `D : E →ₗ[ℝ] F` を `D(f) = f'`（微分）とすると、`D` は線形だが一般に有界ではない
  （例: `fₙ(x)=sin(n x)` で `‖fₙ‖∞=1` だが `‖fₙ'‖∞=n`）

Lean でこれを *完全に* 形式化するには、
* `C¹([0,1])` を型として立てる（`ContDiffMap` / `C^1`-structure など）
* その上に「sup ノルム」を入れて `SeminormedAddCommGroup`/`NormedSpace` を与える
* 微分演算子を `LinearMap` として定義し、`¬ IsBoundedLinearMap` を証明する
という下準備が必要です。

講義ノートではこの例を導入として述べ、
別ファイル（例: `DerivOperator.lean`）で上記の infrastructure を整備してから
`deriv_not_isBounded` を完成させるのが自然です。
-/

end LebesgueNotes
