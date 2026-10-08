+++
id = "prop-weil-pbc-derived-product-representation"
kind = "theorem"
title = "Representation of the derived product of a tower"
order = 1244
uses = ["def-weil-derived-limit", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-kinjective-resolutions", "lem-weil-derived-limit-existence"]
tags = ["latex:proposition"]
+++
Let $\operatorname{Tow}_{A}(T)$ be the tower category of
[def-weil-pbc-adic-coefficient-datum] and let $M_\bullet\in
D(\operatorname{Tow}_{A}(T))$ with a K-injective resolution
[def-weil-pbc-kinjective-resolutions] $M_\bullet\to I_\bullet$ in the abelian
category of towers. Then the derived product $R\!\prod_nM_n$ of
[def-weil-pbc-derived-inverse-limit] is represented by
$\prod_n\operatorname{ev}_n(I_\bullet)$.

(*Source note:* the representing complex is Stacks Project, Derived
Categories, Lemma 13.31.5 (Tag
[0BK6](https://stacks.math.columbia.edu/tag/0BK6)): if the $I_t^\bullet$ are
K-injective complexes and $I^n=\prod_tI_t^n$ exists for all $n$, then
$I^\bullet$ is K-injective and represents the product of the $I_t^\bullet$ in
$D(\mathcal A)$; the termwise description of products is Lemma 13.34.2 (Tag
[07KC](https://stacks.math.columbia.edu/tag/07KC)). Stacks states this for an
arbitrary index set in one abelian category; the form used here applies it to
the levelwise K-injective representatives of the evaluations of one tower
object, the products being taken in the tower category
$\operatorname{Tow}_A(T)$ and the result being read in $D(T_{\Proet},A)$.)

## Proof

By [def-weil-pbc-derived-inverse-limit] the derived product $R\!\prod_nM_n$
is the product of the system $(\operatorname{ev}_nM_\bullet)$ in the
triangulated category $D(T_{\Proet},A)$ attached to the tower category of
[def-weil-pbc-adic-coefficient-datum]. Clause (2) of the derived-limit
existence lemma of the conventions chapter states that in the derived
category of an abelian category with exact countable products the countable
products exist and are represented by termwise products of any
representatives, and clause (3) of the same lemma exhibits
$\prod_n\operatorname{ev}_n(I_\bullet)$ as the termwise product of the
K-injective representatives $\operatorname{ev}_n(I_\bullet)$ of the objects
$\operatorname{ev}_nM_\bullet$; hence that product represents
$R\!\prod_nM_n$.
