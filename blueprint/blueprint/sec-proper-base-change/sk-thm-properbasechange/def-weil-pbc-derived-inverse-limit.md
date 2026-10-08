+++
id = "def-weil-pbc-derived-inverse-limit"
kind = "definition"
title = "Sequential derived inverse limit"
order = 1240
uses = ["def-weil-derived-limit", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-kinjective-resolutions"]
+++
Let $\operatorname{Tow}_{A}(T)$ be the tower category of
[def-weil-pbc-adic-coefficient-datum], with its evaluation functors
$\operatorname{ev}_n$, and let $M_\bullet\in
D(\operatorname{Tow}_{A}(T))$. The evaluations $\operatorname{ev}_nM_\bullet$,
together with the transition maps they carry, exhibit
$(\operatorname{ev}_nM_\bullet)_{n\geq1}$ as an inverse system in the single
triangulated category $D(T_{\Proet},A)$. Its *sequential derived inverse
limit*

$$
 \Rlim M_\bullet
$$

is its derived limit in the sense of the conventions chapter; it is defined
by the Roos triangle applied to $(\operatorname{ev}_nM_\bullet)$. The derived
product $R\!\prod_nM_n$ is the product in $D(T_{\Proet},A)$, computed
termwise by Lemma 13.34.2 (Tag
[07KC](https://stacks.math.columbia.edu/tag/07KC): for $\mathcal A$ abelian
with exact countable products, $D(\mathcal A)$ has countable products,
represented by termwise products of any representatives, with
$H^p(\prod_iK_i)=\prod_iH^p(K_i)$). Both entries are stated for an inverse
system in one triangulated category $D(\mathcal A)$; the form used here is
the system $(\operatorname{ev}_nM_\bullet)$ read off an object of the tower
category $\operatorname{Tow}_A(T)$ over $T_{\Proet}$, and no further
construction is made: the Roos triangle is exactly the triangle recalled
above.
