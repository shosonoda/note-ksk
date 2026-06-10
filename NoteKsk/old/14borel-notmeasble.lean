import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Instances.Real

open scoped BigOperators Topology ENNReal Pointwise

namespace MeasureTheoryLecture

/-!
# Borel 測度の性質と Lebesgue 非可測集合の存在（Vitali）

このファイルは講義ノート（blueprint 前提）として，

* **Borel 可測集合**と **Borel 測度**の基本性質（特に正則性）
* **Lebesgue 可測性**を `NullMeasurableSet`（完備化）として扱う
* **Vitali 集合**による Lebesgue 非可測集合の存在

を **Mathlib の定義・定理に沿って Lean で記述**します．
証明が重い箇所は教育的配慮として `sorry` を残します（blueprint で後に埋める想定）．
-/

noncomputable section

namespace BorelMeasure

/-!
## 1. Borel 可測集合と Borel 測度

`[MeasurableSpace α] [BorelSpace α]` のもとでは，
`MeasurableSet s` は「`s` が Borel 集合」を意味します．

（注意）「Borel 測度」は単に「Borel σ-代数上の測度」です．
多くの解析では「正則 Borel 測度（regular Borel measure）」が重要で，
Mathlib では `μ.Regular` として形式化されています．
-/

section Basics

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
variable (μ : Measure α)

-- 開集合・閉集合が Borel（可測）
lemma measurableSet_of_isOpen {s : Set α} (hs : IsOpen s) : MeasurableSet s :=
  hs.measurableSet

lemma measurableSet_of_isClosed {s : Set α} (hs : IsClosed s) : MeasurableSet s :=
  hs.measurableSet

-- Borel σ-代数は開集合から生成される（既存 API の確認用）
-- #check (borel_eq_generateFrom_of_subbasis : _)

end Basics

/-!
## 2. 正則性（outer regular / regular / inner regular）

Mathlib の主要クラス：
* `μ.OuterRegular` : `μ(A) = inf { μ(U) | A ⊆ U, U open }`（`A` 可測に対して定義）
* `μ.Regular` : 外正則 + 開集合に対する内正則（コンパクト近似） + コンパクト有限
* `μ.InnerRegular` : 可測集合に対してコンパクト近似（内正則）

代表的な定理（講義ノートではここを「正則性の公理化／道具」として使う）：
* `Set.measure_eq_iInf_isOpen`
* `IsOpen.measure_eq_iSup_isCompact`
* `MeasurableSet.measure_eq_iSup_isCompact`
-/

section Regularity

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable (μ : Measure α)

-- 外正則：任意集合に対する開集合近似（`OuterRegular` から導出される形）
theorem measure_eq_iInf_isOpen (A : Set α) [μ.OuterRegular] :
    μ A = ⨅ (U : Set α), ⨅ (_ : A ⊆ U), ⨅ (_ : IsOpen U), μ U := by
  simpa using Set.measure_eq_iInf_isOpen (A := A) (μ := μ)

-- 外正則：μ(A) < r のとき μ(U) < r なる開集合 U ⊇ A を取れる
theorem exists_isOpen_lt_of_lt {A : Set α} {r : ℝ≥0∞} [μ.OuterRegular] (hr : μ A < r) :
    ∃ U ⊇ A, IsOpen U ∧ μ U < r := by
  simpa using Set.exists_isOpen_lt_of_lt (A := A) (μ := μ) (r := r) hr

-- 正則（regular）：開集合はコンパクト集合で内側から近似できる（上限で表す）
theorem isOpen_measure_eq_iSup_isCompact {U : Set α} (hU : IsOpen U) [μ.Regular] :
    μ U = ⨆ (K : Set α), ⨆ (_ : K ⊆ U), ⨆ (_ : IsCompact K), μ K := by
  simpa using hU.measure_eq_iSup_isCompact (μ := μ)

-- 内正則（inner regular）：可測集合はコンパクト集合で内側から近似できる（上限で表す）
theorem measurableSet_measure_eq_iSup_isCompact {A : Set α} (hA : MeasurableSet A) [μ.InnerRegular] :
    μ A = ⨆ (K : Set α), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), μ K := by
  simpa using hA.measure_eq_iSup_isCompact (μ := μ)

-- 型クラス関係の例示：Regular ⇒ OuterRegular, など
example [μ.Regular] : μ.OuterRegular := by infer_instance
example [μ.Regular] : MeasureTheory.IsFiniteMeasureOnCompacts μ := by infer_instance
example [μ.Regular] : μ.InnerRegularCompactLTTop := by infer_instance

-- Hausdorff なら Regular ⇒ WeaklyRegular（閉集合近似ができる）
example [T2Space α] [μ.Regular] : μ.WeaklyRegular := by infer_instance

end Regularity

end BorelMeasure

namespace Lebesgue

/-!
# Lebesgue 測度（`volume`）は「正則 Borel 測度」

Mathlib では `ℝ` に `MeasureSpace` が入り，既定の測度 `volume` が Lebesgue 測度です．
また，適切な一般性で `volume` が正則になるインスタンスが入っています
（局所有限 + σ-コンパクト距離空間 ⇒ 正則，など）．
-/

section

-- `ℝ` 上の Lebesgue 測度の基本インスタンス
example : (volume : Measure ℝ).Regular := by infer_instance
example : (volume : Measure ℝ).OuterRegular := by infer_instance
example : MeasureTheory.IsFiniteMeasureOnCompacts (volume : Measure ℝ) := by infer_instance
example : MeasureTheory.IsLocallyFiniteMeasure (volume : Measure ℝ) := by infer_instance
example : SigmaFinite (volume : Measure ℝ) := by infer_instance

-- 区間の測度計算：`Real.volume_Icc` を使う（`volume (Icc a b) = ofReal (b-a)`）
example : volume (Set.Icc (0 : ℝ) 1) = (1 : ℝ≥0∞) := by
  simp [Real.volume_Icc]

example : volume (Set.Icc (-1 : ℝ) 2) = (3 : ℝ≥0∞) := by
  simp [Real.volume_Icc]

-- 無原子性：`NoAtoms` なら singleton の測度が 0
example : NoAtoms (volume : Measure ℝ) := by infer_instance

example (x : ℝ) : volume ({x} : Set ℝ) = 0 := by
  simpa using (measure_singleton (μ := (volume : Measure ℝ)) x)

end

/-!
# Lebesgue 可測性：完備化（completion）としての `NullMeasurableSet`

古典的には「Lebesgue 可測集合 = Borel 集合 + 零集合で生成される σ-代数」と同値．
Mathlib では「`μ` に関して `NullMeasurableSet`」を Lebesgue 可測性の定式化として使うのが自然．
-/

/-- `s` が Lebesgue 可測（= `volume` に関して null-measurable）であること． -/
def LebesgueMeasurableSet (s : Set ℝ) : Prop :=
  MeasureTheory.NullMeasurableSet s (volume : Measure ℝ)

-- Borel 可測 ⇒ Lebesgue 可測（完備化で可測のまま）
lemma lebesgueMeasurableSet_of_borel {s : Set ℝ} (hs : MeasurableSet s) :
    LebesgueMeasurableSet s := by
  simpa [LebesgueMeasurableSet] using hs.nullMeasurableSet

-- 測度 0 ⇒ Lebesgue 可測
lemma lebesgueMeasurableSet_of_measure_zero {s : Set ℝ} (hs : volume s = 0) :
    LebesgueMeasurableSet s := by
  simpa [LebesgueMeasurableSet] using (MeasureTheory.NullMeasurableSet.of_null hs)

end Lebesgue

namespace Vitali

/-!
# Vitali の定理：Lebesgue 非可測集合の存在（スケッチ）

標準的な流れ（Tao のテキスト等）：

1. `[0,1]` 上で `x ~ y :↔ x - y ∈ ℚ` という同値関係を入れる．
2. 選択公理により，各同値類から代表元を 1 つずつ選び Vitali 集合 `V ⊆ [0,1]` を作る．
3. 有理数 `q ∈ ℚ ∩ [-1,1]` による平行移動族 `V - q`（あるいは `q + V`）は
   * 互いに素（disjoint）
   * `Icc 0 1 ⊆ ⋃ q, (V - q)`
   * `⋃ q, (V - q) ⊆ Icc (-1) 2`
4. Lebesgue 測度は平行移動不変なので `μ(V - q) = μ(V)`．
   もし `V` が（Lebesgue）可測なら，互いに素な可測集合族の測度の和が union の測度に一致し，
   `1 ≤ μ(⋃ q, V - q) ≤ 3` と `μ(⋃ q, V - q) = ∑' q, μ(V)` の矛盾が出る．

ここでは構成と主張を Lean で置き，重い証明は `sorry` にします．
-/

open MeasureTheory Set

/-- 閉区間 `[0,1]` を型（Subtype）として扱う． -/
abbrev I01 := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}

/-- `[0,1]` 上の「差が有理数」同値関係（Vitali 用）． -/
def RatRel (x y : I01) : Prop :=
  ∃ q : ℚ, (y : ℝ) = (x : ℝ) + (q : ℝ)

/-- `RatRel` が同値関係であること（実質的に加法群の計算）． -/
def ratSetoid : Setoid I01 :=
{ r := RatRel
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      refine ⟨0, by simp [RatRel]⟩
    · intro x y h
      rcases h with ⟨q, hq⟩
      refine ⟨-q, ?_⟩
      -- y = x + q から x = y + (-q)
      -- （ここは実数の可換性と `Rat.cast` の整合性を使う）
      -- 教科書的には自明だが Lean では多少の補題が必要になりうるので `sorry` とする
      sorry
    · intro x y z hxy hyz
      rcases hxy with ⟨q₁, hq₁⟩
      rcases hyz with ⟨q₂, hq₂⟩
      refine ⟨q₁ + q₂, ?_⟩
      -- z = x + (q₁ + q₂)
      sorry }

/-- `[0,1] / ~` の商型． -/
abbrev Q01 := Quotient ratSetoid

/-- 各同値類から代表元を選ぶ（Choice）． -/
noncomputable def repr (c : Q01) : I01 :=
  Classical.choose (Quotient.exists_rep c)

lemma mk_repr (c : Q01) : Quotient.mk (repr c) = c := by
  simpa [repr] using (Classical.choose_spec (Quotient.exists_rep c))

/-- Vitali 集合：各同値類の代表元の像（`[0,1]` の部分集合）． -/
noncomputable def vitaliSet : Set ℝ :=
  Set.range (fun c : Q01 => (repr c : ℝ))

lemma vitaliSet_subset_Icc : vitaliSet ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨c, rfl⟩
  exact (repr c).property

/-- 有理数 `q` による「平行移動（前像）」：`x ∈ translate q` ⇔ `q + x ∈ V`．

`measure_preimage_add` をそのまま使える形にしておく．
この集合は集合としては `V - q`（右へ `-q` だけ平行移動）に相当．
-/
noncomputable def translate (q : ℚ) : Set ℝ :=
  (fun x : ℝ => (q : ℝ) + x) ⁻¹' vitaliSet

/-- `translate q` は `[-1,2]` に入る（`q ∈ [-1,1]` のとき）という幾何学的包含． -/
lemma translate_subset_Icc_neg1_2
    (q : ℚ) (hq : ((q : ℚ) : ℝ) ∈ Set.Icc (-1 : ℝ) 1) :
    translate q ⊆ Set.Icc (-1 : ℝ) 2 := by
  -- `q + x ∈ V ⊆ [0,1]` から `x ∈ [-q, 1-q] ⊆ [-1,2]` を示す
  -- ここは一次不等式の計算（有理数の実数埋め込み）なので `linarith` 相当の補題で埋められる
  sorry

/-- Vitali 集合の代表元性：`[0,1]` の任意の点はどれかの `translate q` に入る． -/
lemma Icc01_subset_iUnion_translate :
    Set.Icc (0 : ℝ) 1 ⊆ ⋃ q : {q : ℚ // ((q : ℝ) ∈ Set.Icc (-1 : ℝ) 1)}, translate q := by
  -- 同値類代表元 `repr (mk x)` と `x` の関係から `x ∈ translate (-q)` を作る
  -- Vitali 構成の要（Choice + 商の性質）
  sorry

/-- `q` が異なるとき `translate q` は互いに素（disjoint）． -/
lemma pairwise_disjoint_translate :
    Pairwise (fun q₁ q₂ : {q : ℚ // ((q : ℝ) ∈ Set.Icc (-1 : ℝ) 1)} =>
      Disjoint (translate q₁) (translate q₂)) := by
  -- もしある `x` が両方に入るなら `q₁+x ∈ V` かつ `q₂+x ∈ V` で，
  -- `V` が各同値類から 1 点しか選んでいないことに反する（よって q₁=q₂）
  sorry

/-- Lebesgue 測度（`volume`）の平行移動不変性（`measure_preimage_add` を使用）：
`μ (translate q) = μ V`． -/
lemma volume_translate (q : ℚ) :
    (volume : Measure ℝ) (translate q) = (volume : Measure ℝ) vitaliSet := by
  -- `measure_preimage_add` は
  -- `μ ((fun x => g + x) ⁻¹' A) = μ A` を与える
  simpa [translate] using
    (MeasureTheory.measure_preimage_add (μ := (volume : Measure ℝ)) (g := (q : ℝ)) (A := vitaliSet))

/-!
## 主定理（スケッチ）: Vitali 集合は Lebesgue 可測ではない

最終的には `NullMeasurableSet`（= Lebesgue 完備化）レベルで非可測を示す：

* 仮に `NullMeasurableSet` なら，`toMeasurable` により可測集合で置換しつつ矛盾を出せる
  （このノートでは「可測であると仮定して矛盾」の形で進める）．
-/

theorem vitaliSet_not_lebesgueMeasurable :
    ¬ MeasureTheory.NullMeasurableSet vitaliSet (volume : Measure ℝ) := by
  -- 証明スケッチ：
  -- 1) `hV : NullMeasurableSet V volume` を仮定
  -- 2) 各 `translate q` は（null-)可測になり，しかも互いに素
  -- 3) 可測版の `measure_iUnion`（もしくは `measure_biUnion`）で
  --      `volume (⋃ q, translate q) = ∑' q, volume (translate q)`
  -- 4) `volume_translate` で右辺は `∑' q, volume V`
  -- 5) 包含 `Icc 0 1 ⊆ ⋃ q` と `⋃ q ⊆ Icc (-1) 2` から
  --      `1 ≤ volume(⋃ q) ≤ 3`
  -- 6) `∑' q, volume V` は `0` または `⊤` になり矛盾
  --
  -- ここは Vitali 証明全体の形式化で重いので blueprint で後から埋める：
  sorry

/-- 結論：Lebesgue 非可測集合が存在する． -/
theorem exists_lebesgue_nonmeasurable_set :
    ∃ s : Set ℝ, ¬ MeasureTheory.NullMeasurableSet s (volume : Measure ℝ) := by
  refine ⟨vitaliSet, vitaliSet_not_lebesgueMeasurable⟩

end Vitali

end MeasureTheoryLecture
