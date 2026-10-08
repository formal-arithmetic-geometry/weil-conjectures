+++
id = "prop-weil-pbc-derived-inverse-limit-computation"
kind = "theorem"
title = "Computation of the sequential derived inverse limit"
order = 1241
uses = ["def-weil-derived-limit", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-kinjective-resolutions", "lem-weil-derived-limit-existence"]
tags = ["latex:proposition"]
+++
Let $\operatorname{Tow}_{A}(T)$ be the tower category of
[def-weil-pbc-adic-coefficient-datum] and let $M_\bullet\in
D(\operatorname{Tow}_{A}(T))$. If $M_\bullet\to I_\bullet$ is a K-injective
resolution [def-weil-pbc-kinjective-resolutions] of $M_\bullet$ in the
abelian category of towers, then $\varprojlim_nI_n$ represents the sequential
derived inverse limit $\Rlim M_\bullet$ of
[def-weil-pbc-derived-inverse-limit].

(*Source note:* the model statement is Stacks Project, Derived Categories,
Lemma 13.34.6 (Tag [070M](https://stacks.math.columbia.edu/tag/070M)): for a
complex $K^\bullet$ and the inverse system $I_n^\bullet$ of bounded below
complexes of injectives produced by Lemma 13.29.3,
$I^\bullet=\lim_nI_n^\bullet$ exists, is K-injective, and represents
$R\lim_n\tau_{\ge-n}K^\bullet$; existence of the derived limit is Lemma
13.34.3 (Tag [0BK7](https://stacks.math.columbia.edu/tag/0BK7)), and
functorial K-injective resolutions in a Grothendieck abelian category are
Theorem 19.12.6 (Tag [079P](https://stacks.math.columbia.edu/tag/079P)).
Stacks treats the truncation tower of a single complex of $D(\mathcal A)$,
whereas the form used here resolves an arbitrary object of
$\operatorname{Tow}_A(T)$ in the abelian category of towers over
$T_{\Proet}$; that general-tower form is the one already recorded in the
conventions chapter.)

## Proof

By [def-weil-pbc-derived-inverse-limit] the object $\Rlim M_\bullet$ is the
derived limit of the inverse system $(\operatorname{ev}_nM_\bullet)$ in the
triangulated category $D(T_{\Proet},A)$ attached to the tower category of
[def-weil-pbc-adic-coefficient-datum], an abelian category with exact
countable products. Clause (3) of the derived-limit existence lemma of the
conventions chapter states that a K-injective representative of the system in
the abelian category of towers represents its derived limit; applying it to
the system $(\operatorname{ev}_nM_\bullet)$ and its K-injective
representative $I_\bullet$ exhibits $\varprojlim_nI_n$ as a derived limit of
the system, and clause (1) of the same lemma shows that any two derived
limits of one system are isomorphic.
