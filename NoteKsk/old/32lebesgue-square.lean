/-
  Lebesgue 空間論（続き）:
  * a.e. による同一視 (=ᵐ[μ]) と Setoid / Quotient
  * 本質的上限 essSup と ℒ∞ seminorm
  * 内積空間・Hilbert 空間の基本（Hilbert 基底の存在・中線定理/平行四辺形恒等式）
  * L² は Hilbert 空間

  注意:
  * Mathlib では「a.e. 同一視」そのものは `f =ᵐ[μ] g` という記法で、
    `μ.ae`（co-null sets の Filter）上の `Filter.EventuallyEq` として実装されます。
  * L⁰ (= AEEqFun) は「a.e. 強可測」関数を a.e. 同一視した商として実装されています。
-/

import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.L2Space

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

open scoped BigOperators ENNReal
open Filter MeasureTheory

namespace LebesgueSpaceNotes

/-! ## 1. a.e. 同値関係 (=ᵐ[μ]) を定義から追う -/

section AeEq

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}

/-!
### 1.1 `μ.ae`（a.e. filter）

`μ.ae : Filter α` は「余測度 0（co-null）」集合全体からなるフィルタです。
直観的には
`S ∈ μ.ae` とは「S は a.e. 成り立つ（Sᶜ が null）」を意味します。

この `μ.ae` を使って `∀ᵐ x ∂μ, P x`（a.e. で P）が定義されます。
-/

/-- a.e. の定義: `∀ᵐ x ∂μ, P x` は `P` が `μ.ae` 上で eventually 成り立つこと。 -/
example (P : α → Prop) : (∀ᵐ x ∂μ, P x) = (Filter.Eventually P (MeasureTheory.ae μ)) := rfl

/-!
### 1.2 a.e. 等号 `f =ᵐ[μ] g`

`f =ᵐ[μ] g` は「`f x = g x` が a.e. 成り立つ」を表す記法で、
実体は `Filter.EventuallyEq` です。
-/

variable (f g h : α → β)

/-- `f =ᵐ[μ] g` の展開（定義そのもの）。 -/
example : (f =ᵐ[μ] g) = Filter.EventuallyEq (MeasureTheory.ae μ) f g := rfl

/-- “集合として”書けば `{x | f x = g x}` が co-null。 -/
example : (f =ᵐ[μ] g) ↔ (∀ᵐ x ∂μ, f x = g x) := Iff.rfl

/-!
### 1.3 `=ᵐ[μ]` は同値関係

`Filter.EventuallyEq` は一般に同値関係なので、`=ᵐ[μ]` も reflexive / symmetric / transitive。
Lean では `.refl` / `.symm` / `.trans` が使えます。
-/

/-- 反射律 -/
lemma aeEq_refl (f : α → β) : f =ᵐ[μ] f := by
  simp

/-- 対称律 -/
lemma aeEq_symm (hfg : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  hfg.symm

/-- 推移律 -/
lemma aeEq_trans (hfg : f =ᵐ[μ] g) (hgh : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  hfg.trans hgh

/-!
### 1.4 `Setoid` と `Quotient`（「a.e. で同一視」した型）

講義ノート的には「関数全体 `α → β` を a.e. 同一視した商」をまず作っておくと便利です。
（ただし Mathlib の `AEEqFun` は **a.e. 強可測** に限定してから商を取ります。）
-/

/-- `α → β` 上の a.e. 同値関係を `Setoid` として束ねたもの。 -/
def aeEqSetoidFun (μ : Measure α) (β : Type*) : Setoid (α → β) where
  r := fun f g => f =ᵐ[μ] g
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f; simp
    · intro f g hfg; exact hfg.symm
    · intro f g h hfg hgh; exact hfg.trans hgh

/-- “a.e. 同一視した関数”の素朴な商（講義用の簡易版）。 -/
abbrev AEFun (μ : Measure α) (β : Type*) : Type _ :=
  Quotient (aeEqSetoidFun (μ := μ) (β := β))

/-!
### 1.5 Mathlib の `AEEqFun`（= L⁰）

Mathlib の `AEEqFun` は「**a.e. 強可測**」関数の部分型
`{f : α → β // AEStronglyMeasurable f μ}`
を `=ᵐ[μ]` で商にしたものです。

* `μ.aeEqSetoid β` : その Setoid
* `AEEqFun α β μ` : その商（記法 `α →ₘ[μ] β`）
-/

section
variable [TopologicalSpace β]

/-- Mathlib 側の Setoid（a.e. 強可測に制限して商を取る）。 -/
#check MeasureTheory.Measure.aeEqSetoid

/-- L⁰ 空間（a.e. 強可測関数の a.e. 同値類）。 -/
#check MeasureTheory.AEEqFun
#check (α →ₘ[μ] β)

/-- `AEEqFun.mk` で「関数 + a.e. 強可測性」から同値類を作る。 -/
#check MeasureTheory.AEEqFun.mk

end

end AeEq

/-! ## 2. L∞: 本質的上限 `essSup` と ℒ∞ seminorm -/

section Linfty

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-!
### 2.1 `essSup`

`essSup f μ` は `f : α → β`（`β` が条件付き完備束）の本質的上限。
Mathlib では
`essSup f μ := Filter.limsup f (ae μ)`
として定義されています。

直観: 「a.e. で `f x ≤ c` となるような定数 `c` の中で最小のもの」。
-/

variable {β : Type*} [ConditionallyCompleteLattice β] (f : α → β)

#check MeasureTheory.essSup

/-- 定義の等式（そのまま）。 -/
lemma essSup_def : MeasureTheory.essSup f μ = Filter.limsup f (MeasureTheory.ae μ) := by
  rfl

/-- a.e. で一致すれば essSup も一致する（a.e. 同一視と相性が良い）。 -/
#check MeasureTheory.essSup_congr_ae

/-!
### 2.2 ℒ∞ seminorm（`eLpNormEssSup`）

Mathlib の ℒp seminorm（`eLpNorm`）は `p = ∞` のとき本質的上限で与えられます。
特に
`eLpNormEssSup f μ = essSup (fun x => ‖f x‖ₑ) μ`
です（`‖ ‖ₑ` は ENorm: 値が `ENNReal` のノルム）。
-/

variable {ε : Type*} [ENorm ε] (g : α → ε)

#check MeasureTheory.eLpNormEssSup
#check MeasureTheory.eLpNormEssSup_eq_essSup_enorm

/-- `ℒ∞` seminorm の定義式（既存補題で）。 -/
lemma eLpNormEssSup_eq_essSup :
    MeasureTheory.eLpNormEssSup g μ
      = MeasureTheory.essSup (fun x => ‖g x‖ₑ) μ := by
  simpa using MeasureTheory.eLpNormEssSup_eq_essSup_enorm (f := g) (μ := μ)

/-!
（講義ノートの言い方）
* `‖g‖_{∞,μ} := essSup (‖g x‖) μ`
* `g ∈ L∞` は `‖g‖_{∞,μ} < ∞`（a.e. 可測性も合わせて要求）
  という形で `MemLp g ⊤ μ` にまとめられている。
-/

#check MeasureTheory.MemLp

end Linfty

/-! ## 3. 内積空間・Hilbert 空間の基本 -/

section HilbertBasics

/-!
### 3.1 内積空間と Hilbert 空間（Lean のクラス）

Mathlib では「Hilbert 空間」という専用クラスは立てず、

* `[InnerProductSpace 𝕜 E]`（内積空間）
* `[CompleteSpace E]`（距離空間として完備）

の両方を持つものを “Hilbert space” として扱います。
-/

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
### 3.2 中線定理（平行四辺形恒等式）

あなたの意図する「中線定理」は、Hilbert 幾何の基本恒等式としては
**平行四辺形恒等式**を指すのが自然です。

Mathlib には
* `parallelogram_law`（内積で書いた形）
* `parallelogram_law_with_norm`（ノルムで書いた形）

が用意されています。
-/

#check parallelogram_law
#check parallelogram_law_with_norm

/-- ノルム版：`‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)` の Lean 版（`*` で書かれている）。 -/
lemma parallelogram_law_norm (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖
      = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  simpa using parallelogram_law_with_norm (𝕜 := 𝕜) (x := x) (y := y)

/-!
### 3.3 直交基底（Hilbert 基底）の存在

Mathlib では Hilbert 空間の“直交基底”は `HilbertBasis` として整備されており、
古典的選択に基づいて「存在」を与える定理が `exists_hilbertBasis` です。

（ファイル: `Mathlib/Analysis/InnerProductSpace/l2Space.lean` など）
-/

section
variable [CompleteSpace E]

#check HilbertBasis
#check exists_hilbertBasis

/--
`exists_hilbertBasis` から「ある HilbertBasis を一つ取る」例。
（講義ノートで “基底を固定して議論する” 場合に有用）
-/
noncomputable def someHilbertBasis :
    ∃ (ι : Type _), HilbertBasis ι 𝕜 E := by
  classical
  -- `exists_hilbertBasis` の返り値の形に応じて `rcases` の形は調整してください。
  -- 多くの環境では `∃ ι, Nonempty (HilbertBasis ι 𝕜 E)` を返すので、そこで `choice` します。
  rcases (exists_hilbertBasis (𝕜 := 𝕜) (E := E)) with ⟨ι, hι⟩
  exact ⟨ι, Classical.choice hι⟩

end

end HilbertBasics

/-! ## 4. L² 空間は Hilbert 空間である -/

section L2IsHilbert

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
### 4.1 L² 空間 `α →₂[μ] E`

Mathlib では `L²` は（Bochner 版も含めて）`L2Space` に実装されており、
型としては `α →₂[μ] E`（記法）を使います。

この型には
* `NormedAddCommGroup`
* `InnerProductSpace`
が入り、さらに `E` が完備なら `CompleteSpace` も入るので Hilbert です。
-/

#check (α →₂[μ] E)

/-- `L²` は内積空間（Mathlib のインスタンス）。 -/
example : InnerProductSpace 𝕜 (α →₂[μ] E) := by
  infer_instance

/-- `E` が完備なら `L²` も完備（よって Hilbert）。 -/
example [CompleteSpace E] : CompleteSpace (α →₂[μ] E) := by
  infer_instance

/--
まとめ：`E` が Hilbert（内積 + 完備）なら `L²(μ;E)` も Hilbert。
（Lean では「Hilbert である」という Prop はなく、インスタンスで表現する。）
-/
example [CompleteSpace E] : True := by
  -- ここで `infer_instance` で必要な構造が全て入ることを確認できる
  haveI : InnerProductSpace 𝕜 (α →₂[μ] E) := by infer_instance
  haveI : CompleteSpace (α →₂[μ] E) := by infer_instance
  trivial

end L2IsHilbert

end LebesgueSpaceNotes
