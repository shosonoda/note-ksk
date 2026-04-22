#　質問
Lebesgue自身や，同時代の人たちが測度論を構成する際に，面積（測度）が満たすべき要求仕様として以下のようなものを目指したとされます：

- （全域性）すべての部分集合 $A \subset \mathbb R^d$ に対し，面積 $\mu(A)$ が定まる
- （非負性）$0 \le \mu(A) \le \infty$
- （加法性）$\mu\left( \bigsqcup_{i=1}^\infty A_i \right) = \sum_{i=1}^\infty \mu(A_i)$
- （合同変換不変性）$\mu( T A + c ) = \mu(A)$
- （Euclid幾何学との整合性）可算集合のような薄い集合の体積は $0$

典型的な教科書等を調査して，上記項目の記述の妥当性を調査してください．用語に語弊があるようであれば，適切に訂正してください．また，上記の他にもあれば追加してください．

---
# 回答

結論から言うと、挙げられた5項目は**「Lebesgue測度の最終的な定義」**としては不正確ですが、**「教科書が最初に提示する“理想的な体積概念”」**としてはかなり妥当です。実際、Folland は「理想的には」 \(E\subset \mathbb R^n\) の各集合に数 \(\mu(E)\) を割り当て、可算加法性・合同（剛体運動）不変性・単位立方体の測度 \(1\) を満たしたい、と明示したうえで、それらは両立しないと説明しています。Tao も同様に “problem of measure” を、一般の \(E\subset\mathbb R^d\) に「正しい」測度を与える問題として提示し、標準的解決は「すべての部分集合を測ることを諦めて、可測集合に制限すること」だと述べています。Hunter も、全ての部分集合上の可算加法的・等長変換不変な測度は作れないと要約しています。([ia802900.us.archive.org][1])

ただし、これをそのまま「Lebesgue 自身や同時代人の**要求仕様の箇条書き**」とみなすのは少し言い過ぎです。Borel の 1898 年の有名な言葉では、「前述の考えで測度を定義できる集合を measurable と呼ぶ」としつつ、それが他の集合に測度を与えられないことを意味するわけではない、とされています。つまり同時代にはすでに、「まず“測れる集合のクラス”を取り出す」という発想がありました。また Sternberg の講義ノートでも、Lebesgue の 1902 年の可測性の定義と Carathéodory の 1914 年の定義が区別されており、歴史的には最初から現代的な公理リストで始まったわけではありません。([Princeton University Press Assets][2])

各項目について見ると、次のように直すのがよいです。

1. **（全域性）**
   　この項目は、そのままだと不正確です。**測度 \(\mu\)** について「すべての部分集合 \(A\subset\mathbb R^d\) に対して \(\mu(A)\) が定まる」は、少なくとも通常の ZFC 的な教科書文脈では成立しません。正しいのは、**外測度 \(\mu^*\)** なら全ての部分集合に定義できるが、**可算加法的な測度 \(\mu\)** は可測集合の \(\sigma\)-代数の上にしか定義できない、ということです。Hunter はまさに「全ての部分集合上には無理だが、\(\mathbb R^n\) の全ての部分集合上に等長不変・可算劣加法的な外測度は作れ、その後で可測集合の \(\sigma\)-代数 \(L(\mathbb R^n)\) に制限する」と説明しています。したがって、ここは **「理想的には全域的であってほしい」** あるいは **「外測度は全域的」** に直すのが適切です。なお Tao は、選択公理のもとでは可算加法性と平行移動不変性を保ったまま全ての部分集合へ拡張できないことも明言しています。([math.ucdavis.edu][3])

2. **（非負性）**
   　これは妥当です。ただし、教科書の標準的な定義では普通
   \[
   \mu:\mathcal M\to[0,\infty],\qquad \mu(\varnothing)=0
   \]
   を明記します。Tao も Axler も、測度の定義として「空集合に 0 を与え、互いに素な可測集合列に対して可算加法的」と書いています。したがって、この項目は **「非負性」に \(\mu(\varnothing)=0\) を加える** のが自然です。([What's new][4])

3. **（加法性）**
   　趣旨は正しいです。ただし正確には
   \[
   \mu!\left(\bigsqcup_{i=1}^\infty A_i\right)=\sum_{i=1}^\infty \mu(A_i)
   \]
   は **\(A_i\) が可測で pairwise disjoint** のときに要求されます。ここで大事なのは「有限加法性」ではなく**可算加法性**で、Folland は「有限加法性に弱めるのはよくない。理論の極限・連続性の結果がうまく働くのは可算加法性のおかげだ」とはっきり述べています。Rudin も、可測集合族が可算和・可算交わり・補集合で閉じており、そのうえで長さが可算加法的に拡張されることを、Lebesgue 理論の crucial な集合論的性質として挙げています。([ia802900.us.archive.org][1])

4. **（合同変換不変性）**
   　趣旨はよいですが、式の書き方は直した方がよいです。
   \[
   \mu(TA+c)=\mu(A)
   \]
   と書くと、\(T\) が任意の線形変換に見えてしまいます。もし \(T\) が一般の線形変換なら、正しい式は通常
   \[
   \mu(TA)=|\det T|,\mu(A)
   \]
   です。したがって、ここは **「等長変換不変性」** あるいは **「剛体運動不変性」** と書き、
   \[
   \mu(UA+a)=\mu(A)\qquad(U\in O(d),,a\in\mathbb R^d)
   \]
   のように書くのが正確です。Folland の理想条件も「translation, rotation, reflection」による congruence ですし、Hunter と Princeton のテキストは、平行移動不変性を先に示し、その後で回転・反射不変性、したがって全ての isometry に対する不変性を述べています。さらに dilation については \(\mu(\delta E)=\delta^d\mu(E)\) も標準的性質です。([ia802900.us.archive.org][1])

5. **（Euclid 幾何学との整合性）**
   　ここは一番言い換えた方がよいです。教科書で普通に置かれるのは、
   　- **単位立方体の測度が \(1\)**、
   　- **長方形・直方体の測度が辺長の積**、
   　- **初等幾何で求まる単純な図形では通常の長さ・面積・体積と一致する**、
   という条件です。Folland は理想条件として \(\mu(Q)=1\) を置き、Princeton の章も「単純な集合の体積は初等計算の値と一致する」と述べています。これに対して「可算集合のような薄い集合の体積は 0」は、むしろ**その帰結**として出てくる性質です。Axler は「任意の可算部分集合は外測度 0」と明示していますし、Princeton では「外測度 0 の集合の任意の部分集合も可測」としています。よってこの項目は、**「矩形・立方体で通常の体積と一致する」** に置き換え、可算集合の測度 0 は帰結として別記するのがよいです。([Measure][5])

そのうえで、典型的な教科書調査からは、少なくとも次の項目を追加した方がよいです。

* **（定義域）\(\sigma\)-代数上で定義されること**
  Rudin や Princeton の章では、可測集合の族が可算和・可算交わり・補集合で閉じること自体が中心的です。現代の測度は「全冪集合上の関数」ではなく、**\(\sigma\)-代数上の可算加法的集合関数**として定義されます。([perso.telecom-paristech.fr][6])

* **（完全性）零集合の部分集合も可測であること**
  Lebesgue 測度を Borel 測度の completion とみるのが普通で、その意味で「零集合の部分集合も測れる」は重要です。Axler は、Borel 測度と Lebesgue 測度の違いは主としてこの completion にあると説明しています。([Measure][5])

* **（正則性・近似可能性）開集合・閉集合・コンパクト集合で近似できること**
  Princeton の章では、可測集合 \(E\) は外側から開集合、内側から閉集合やコンパクト集合で任意精度に近似できることが強調されています。これは「幾何学との整合性」を、可算集合 0 よりもずっと本質的に表す性質です。([Princeton University Press Assets][2])

* **（スケーリング / 線形変換への共変性）**
  等長変換不変性だけでなく、\(\mu(\delta E)=\delta^d\mu(E)\)、さらに一般に \(\mu(LE)=|\det L|\mu(E)\) という変換則も、現代の教科書では重要な構造として扱われます。これは初期公理というより、構成後に示される基本性質と見るのが普通です。([Princeton University Press Assets][2])

歴史的な言い方をもう少し忠実にするなら、Lebesgue 自身の出発点は、現代風の「公理リスト」というより、**区間被覆による外測度の定義**と、**上からの見積もりと下からの見積もりが一致する集合を measurable とする**という構成です。Sternberg はこれを「Lebesgue の 1902 年の可測性の定義」として Carathéodory の 1914 年の定義と区別して紹介していますし、Lebesgue の後年の説明を引く MAA の資料でも、集合を区間で覆って長さの総和の下限を取り、補集合側からの下界と一致するとき measurable とする、という説明が見えます。だから、あなたのリストは**歴史そのものの逐語的再現ではなく、現代の教科書が再構成した“動機づけの仕様”**だと理解するのがいちばん正確です。([people.math.harvard.edu][7])

したがって、教科書的に最も無難な書き換えは、たとえば次のようになります。

* 理想的には、\(\mathbb R^d\) の各集合に「体積」を与えたいが、実際には **外測度は全ての部分集合に、測度は十分大きい \(\sigma\)-代数に** 定義する。([math.ucdavis.edu][3])
* 測度は \([0,\infty]\)-値、\(\mu(\varnothing)=0\)、可測集合列に対して **可算加法的** である。([What's new][4])
* **単位立方体の測度は \(1\)**、より一般に矩形の測度は辺長の積で、初等幾何の体積と一致する。([ia802900.us.archive.org][1])
* **剛体運動不変** であり、さらに一般の線形変換に対しては (|\det|) に従って変換する。([math.ucdavis.edu][3])
* **零集合は無視でき**、可算集合は測度 0、かつ Lebesgue 測度では零集合の部分集合も可測である。([Measure][5])
* 可測集合は **開集合・閉集合・コンパクト集合で近似可能** である。([Princeton University Press Assets][2])

必要なら次に、この内容を **「歴史的記述としての妥当性」** と **「現代的定義としての正確性」** の二列で対比表にして整理します。

[1]: https://ia802900.us.archive.org/17/items/real-analysis-textbooks/Real%20Analysis%20-%20G.%20B.%20Folland.pdf "https://ia802900.us.archive.org/17/items/real-analysis-textbooks/Real%20Analysis%20-%20G.%20B.%20Folland.pdf"
[2]: https://assets.press.princeton.edu/chapters/s8008.pdf "https://assets.press.princeton.edu/chapters/s8008.pdf"
[3]: https://www.math.ucdavis.edu/~hunter/measure_theory/measure_notes_ch2.pdf "https://www.math.ucdavis.edu/~hunter/measure_theory/measure_notes_ch2.pdf"
[4]: https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-126-tao5-measure-book.pdf "https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-126-tao5-measure-book.pdf"
[5]: https://measure.axler.net/MIRA.pdf "https://measure.axler.net/MIRA.pdf"
[6]: https://perso.telecom-paristech.fr/decreuse/_downloads/c22155fef582344beb326c1f44f437d2/rudin.pdf "https://perso.telecom-paristech.fr/decreuse/_downloads/c22155fef582344beb326c1f44f437d2/rudin.pdf"
[7]: https://people.math.harvard.edu/~shlomo/212a/11.pdf "https://people.math.harvard.edu/~shlomo/212a/11.pdf"
