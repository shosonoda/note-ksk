import Mathlib.Analysis.BoxIntegral.Basic
import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.NumberTheory.Real.Irrational

/-!
# Riemann 積分の復習（Jordan 測度/内容積 → Riemann 和 → 積分）

このファイルでは，Lebesgue 積分論に入る前段として，

* Jordan 的な「内容積」（矩形 box への有限加法的な体積）を `BoxIntegral.BoxAdditiveMap` として扱い，
* それに基づく Riemann 和（tagged partition の和）と
* Riemann 積分（`IntegrationParams.Riemann` による box integral）

を mathlib の既存の形式化に沿って定義し，基本性質を Lean で記述する．

最後に，Dirichlet 関数（有理点で 1，無理点で 0）が Riemann 積分できないことや，
Riemann 積分の限界（極限操作の不安定さ）を *定理の形で宣言* しておく．

（証明が長い箇所は `sorry` にして blueprint で管理する想定．）
-/

open scoped BigOperators
open Set

namespace LebesgueNotes
namespace RiemannPrelude

/-! ## 0. 準備：`ℝⁿ` を `ι → ℝ` として扱う -/

variable {ι : Type*} [Fintype ι]
local notation "ℝⁿ" => (ι → ℝ)

/-! ## 1. Jordan 的な体積：矩形 box 上の有限加法族（内容積）

`BoxIntegral` では，矩形 box 上の（分割に関して）加法的な体積を
`BoxIntegral.BoxAdditiveMap` として抽象化している．

* `BoxIntegral.BoxAdditiveMap.volume` は，通常の Euclidean volume（長さ/面積/体積）に対応する
  box-additive map であり，Jordan 的な内容積の役割を果たす．

この `volume` は値域が `E →L[ℝ] E`（連続線形写像）である点に注意：
Riemann 和を一般のノルム空間値関数へ拡張するためである．
-/

noncomputable def jordanVolume : BoxIntegral.BoxAdditiveMap ι (ℝ →L[ℝ] ℝ) ⊤ :=
  BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ)

/-- Jordan 的な box の（スカラー）体積：`volume` を `1` に作用させたもの． -/
noncomputable def boxVolume (I : BoxIntegral.Box ι) : ℝ :=
  (jordanVolume (ι := ι) I) 1

/-! ## 2. Riemann 積分：`BoxIntegral` による定義

`IntegrationParams.Riemann` は
* すべての小 box の直径が一定の上界で抑えられる（古典的 Riemann 風）こと，
* tag がそれぞれの小 box の閉包に入る（Henstock 条件）

を課すパラメータである（mathlib の doc 参照）．

このとき `BoxIntegral.integral` は Riemann 積分そのものとして理解できる．
-/

noncomputable def riemannIntegral (I : BoxIntegral.Box ι) (f : ℝⁿ → ℝ) : ℝ :=
  BoxIntegral.integral (I := I) BoxIntegral.IntegrationParams.Riemann f (jordanVolume (ι := ι))

/-- Riemann 可積分性（box 上）． -/
def RiemannIntegrable (I : BoxIntegral.Box ι) (f : ℝⁿ → ℝ) : Prop :=
  BoxIntegral.Integrable (I := I) BoxIntegral.IntegrationParams.Riemann f (jordanVolume (ι := ι))

/-- `f` の Riemann 積分が `y` に等しい，という `HasIntegral` 版． -/
def HasRiemannIntegral (I : BoxIntegral.Box ι) (f : ℝⁿ → ℝ) (y : ℝ) : Prop :=
  BoxIntegral.HasIntegral (I := I) BoxIntegral.IntegrationParams.Riemann f (jordanVolume (ι := ι)) y

/-! ## 3. 基本性質（線形性・定数関数）

以下はほぼ `BoxIntegral` の一般定理を `Riemann` パラメータと `volume` に特殊化しているだけ． -/

section BasicLemmas

variable (I : BoxIntegral.Box ι) (f g : ℝⁿ → ℝ)

theorem riemannIntegrable_const (c : ℝ) : RiemannIntegrable (ι := ι) I (fun _ => c) := by
  simpa [RiemannIntegrable, jordanVolume] using
    (BoxIntegral.integrable_const
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ))
      c)

theorem riemannIntegral_const (c : ℝ) :
    riemannIntegral (ι := ι) I (fun _ => c)
      = (jordanVolume (ι := ι) I) c := by
  -- `integral_const` は一般の体積 `vol` に対して `vol I c` を返す
  simpa [riemannIntegral, jordanVolume] using
    (BoxIntegral.integral_const
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ))
      c)

theorem riemannIntegrable_zero : RiemannIntegrable (ι := ι) I (fun _ => (0 : ℝ)) := by
  simpa [RiemannIntegrable, jordanVolume] using
    (BoxIntegral.integrable_zero
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ)))

theorem riemannIntegral_zero :
    riemannIntegral (ι := ι) I (fun _ => (0 : ℝ)) = 0 := by
  simpa [riemannIntegral, jordanVolume] using
    (BoxIntegral.integral_zero
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ)))

theorem riemannIntegrable_add
    (hf : RiemannIntegrable (ι := ι) I f) (hg : RiemannIntegrable (ι := ι) I g) :
    RiemannIntegrable (ι := ι) I (fun x => f x + g x) := by
  -- dot-style lemma: `hf.add hg`
  simpa [RiemannIntegrable, jordanVolume] using hf.add hg

theorem riemannIntegral_add
    (hf : RiemannIntegrable (ι := ι) I f) (hg : RiemannIntegrable (ι := ι) I g) :
    riemannIntegral (ι := ι) I (fun x => f x + g x)
      = riemannIntegral (ι := ι) I f + riemannIntegral (ι := ι) I g := by
  simpa [riemannIntegral, RiemannIntegrable, jordanVolume] using
    (BoxIntegral.integral_add
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ))
      hf hg)

theorem riemannIntegrable_neg
    (hf : RiemannIntegrable (ι := ι) I f) : RiemannIntegrable (ι := ι) I (fun x => - f x) := by
  simpa [RiemannIntegrable, jordanVolume] using hf.neg

theorem riemannIntegral_neg
    (hf : RiemannIntegrable (ι := ι) I f) :
    riemannIntegral (ι := ι) I (fun x => - f x)
      = - riemannIntegral (ι := ι) I f := by
  simpa [riemannIntegral, RiemannIntegrable, jordanVolume] using
    (BoxIntegral.integral_neg
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ))
      hf)

theorem riemannIntegrable_sub
    (hf : RiemannIntegrable (ι := ι) I f) (hg : RiemannIntegrable (ι := ι) I g) :
    RiemannIntegrable (ι := ι) I (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using (riemannIntegrable_add (I := I) (f := f) (g := fun x => -g x) hf
    (riemannIntegrable_neg (I := I) (f := g) hg))

theorem riemannIntegral_sub
    (hf : RiemannIntegrable (ι := ι) I f) (hg : RiemannIntegrable (ι := ι) I g) :
    riemannIntegral (ι := ι) I (fun x => f x - g x)
      = riemannIntegral (ι := ι) I f - riemannIntegral (ι := ι) I g := by
  simpa [sub_eq_add_neg] using (by
    -- `integral_sub` があるのでそれを直接使ってもよい（ここでは add/neg から再構成）
    simpa [sub_eq_add_neg] using
      (by
        have hneg : RiemannIntegrable (ι := ι) I (fun x => -g x) := riemannIntegrable_neg (I := I) (f := g) hg
        simpa [sub_eq_add_neg] using
          (riemannIntegral_add (I := I) (f := f) (g := fun x => -g x) hf hneg)))

/-- 連続関数は（Riemann）可積分． -/
theorem riemannIntegrable_of_continuousOn
    {f : ℝⁿ → ℝ} (hf : ContinuousOn f (BoxIntegral.Box.Icc I)) :
    RiemannIntegrable (ι := ι) I f := by
  simpa [RiemannIntegrable, jordanVolume] using
    (BoxIntegral.integrable_of_continuousOn
      (I := I)
      (l := BoxIntegral.IntegrationParams.Riemann)
      (vol := BoxIntegral.BoxAdditiveMap.volume (ι := ι) (E := ℝ))
      hf)

end BasicLemmas

/-! ## 4. 1次元区間 `[a,b]` の box と Dirichlet 関数

mathlib の box は `(l,u]` 型（半開区間）だが，Riemann 積分の議論では
閉区間・半開区間の違いは境界の体積 0 によって（Lebesgue 的には）吸収される．

ここでは 1次元 `ι = Unit` の box を「区間」と見なして Dirichlet 関数の限界を表現する． -/

namespace OneDim

/-- 1次元の box：`(a,b]` に相当する `BoxIntegral.Box Unit` -/
def intervalBox (a b : ℝ) (hab : a < b) : BoxIntegral.Box Unit :=
  { lower := fun _ => a
    upper := fun _ => b
    lower_lt_upper := by
      intro _
      simpa using hab }

/-- Dirichlet 関数：有理点で 1，それ以外（無理点）で 0． -/
def dirichlet (x : ℝ) : ℝ :=
  if x ∈ Set.range Rat.cast then (1 : ℝ) else 0

/-- `ι = Unit` 上の Dirichlet（`x ()` を 1次元座標とみなす）． -/
def dirichletU (x : Unit → ℝ) : ℝ :=
  dirichlet (x ())

/-!
### Dirichlet 関数が Riemann 積分できない（限界 1）

古典的議論：
任意の分割に対して，各小区間には有理点も無理点も存在するので，
下 Darboux 和は 0，上 Darboux 和は `b-a` となり一致しない．
ゆえに Riemann 可積分ではない．

`BoxIntegral` の枠では「十分細かい tagged partition による積分和が Cauchy でない」ことを示す．
（証明は長いので blueprint 管理を想定して `sorry` にしておく．）
-/

/-- Dirichlet 関数は非退化区間上で Riemann 可積分ではない． -/
theorem not_riemannIntegrable_dirichlet (a b : ℝ) (hab : a < b) :
    ¬ RiemannIntegrable (ι := Unit) (intervalBox a b hab) dirichletU := by
  classical
  -- proof sketch (to be formalized):
  -- 1. 任意の `r > 0` に対し，mesh が十分小さい Henstock tagged partition をとる．
  -- 2. 各小区間に「有理 tag」を選べば積分和は `b-a` に近くなる．
  -- 3. 各小区間に「無理 tag」を選べば積分和は 0 に近くなる．
  -- 4. よって積分和は Cauchy にならず，`Integrable` に反する．
  sorry

/-!
### 逐点極限で壊れる（限界 2：DCT/単調収束が（そのままでは）成り立たない）

Dirichlet 関数は次のような「各段階で Riemann 可積分な関数列」の逐点極限として得られる：

* `f_n(x) = 1`  if `x` が分母 ≤ n の有理数，
* `f_n(x) = 0`  otherwise.

各 `f_n` は不連続点が有限（区間において有限個の有理数）なので Riemann 可積分で積分は 0．
しかし極限は Dirichlet 関数で Riemann 可積分でない．

ここでは「限界の主張」を定理の形で宣言しておき，後で必要な補題（分母制限有理数の有限性，
有限不連続関数の可積分性など）を積み上げる．
-/

/-- 「分母 ≤ n の有理数」の集合（`Set.range` で扱う）に依存した近似 Dirichlet． -/
def dirichletApprox (n : ℕ) (x : ℝ) : ℝ :=
  if ∃ (q : ℚ), (q.den : ℕ) ≤ n ∧ (Rat.cast q : ℝ) = x then (1 : ℝ) else 0

def dirichletApproxU (n : ℕ) (x : Unit → ℝ) : ℝ :=
  dirichletApprox n (x ())

/-- 近似 `dirichletApproxU n` は各 n で Riemann 可積分（主張）． -/
theorem riemannIntegrable_dirichletApprox (a b : ℝ) (hab : a < b) (n : ℕ) :
    RiemannIntegrable (ι := Unit) (intervalBox a b hab) (dirichletApproxU n) := by
  classical
  -- TODO: 不連続点が有限個であることからの Riemann 可積分性を形式化する
  sorry

/-- 近似 `dirichletApproxU n` の Riemann 積分は 0（主張）． -/
theorem riemannIntegral_dirichletApprox_eq_zero (a b : ℝ) (hab : a < b) (n : ℕ) :
    riemannIntegral (ι := Unit) (intervalBox a b hab) (dirichletApproxU n) = 0 := by
  classical
  -- TODO: 区間上で有限集合の indicator の積分が 0 であることを示す
  sorry

/-- 逐点極限は Dirichlet 関数（主張）． -/
theorem tendsto_dirichletApprox_pointwise (x : Unit → ℝ) :
    Filter.Tendsto (fun n : ℕ => dirichletApproxU n x) Filter.atTop (Filter.pure (dirichletU x)) := by
  classical
  -- TODO: `x` が有理ならある段階で 1，無理なら常に 0 を使う
  sorry

/-- Riemann 積分は一般に逐点極限と交換できない（Dirichlet による反例）． -/
theorem not_dominated_convergence_for_riemann (a b : ℝ) (hab : a < b) :
    (∀ n, RiemannIntegrable (ι := Unit) (intervalBox a b hab) (dirichletApproxU n)) ∧
    (∀ n, riemannIntegral (ι := Unit) (intervalBox a b hab) (dirichletApproxU n) = 0) ∧
    (¬ RiemannIntegrable (ι := Unit) (intervalBox a b hab) dirichletU) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; exact riemannIntegrable_dirichletApprox (a := a) (b := b) hab n
  · intro n; exact riemannIntegral_dirichletApprox_eq_zero (a := a) (b := b) hab n
  · exact not_riemannIntegrable_dirichlet (a := a) (b := b) hab

/-!
### （補足）無理数の稠密性（後で Dirichlet の非可積分性の証明に使う）

`NumberTheory.Real.Irrational` には `exists_irrational_btwn` があるので，
任意の区間に無理数が存在することが Lean でそのまま使える．
-/

/-- 任意の `a < b` の間に無理数が存在する． -/
theorem exists_irrational_btwn' {a b : ℝ} (hab : a < b) : ∃ x, Irrational x ∧ a < x ∧ x < b := by
  simpa using exists_irrational_btwn hab

end OneDim
end RiemannPrelude
end LebesgueNotes
