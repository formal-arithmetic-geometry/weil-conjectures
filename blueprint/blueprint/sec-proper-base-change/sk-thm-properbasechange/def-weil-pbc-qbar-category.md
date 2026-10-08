+++
id = "def-weil-pbc-qbar-category"
kind = "definition"
title = "Qbar-l coefficient category"
order = 1311
uses = ["def-weil-karoubi-envelope", "def-weil-pbc-common-stage-cones", "def-weil-pbc-finite-stage-pair-category"]
+++
For $\alpha\in\Qlb$ and $f=[M,u]$ in $\mathcal P_T$, choose a finite field
$N\supset M,\Ql(\alpha)$ and define
$$
 \alpha f=[N,\alpha u_N].
$$
Define
$$
 \Dbc(T,\Qlb)=\mathcal P_T:
$$
an object is a pair $(E,K)$ with $K\in\Dbc(T,E)$ at a finite stage $E$, and
a morphism is a class $[M,u]$ of
[def-weil-pbc-finite-stage-pair-category]. The shift is that of
[def-weil-pbc-common-stage-cones] and the distinguished triangles are the
common-stage cone triangles of [def-weil-pbc-common-stage-cones]; that these
data satisfy the Verdier axioms and give an ordinary triangulated category
is [thm-weil-pbc-verdier-axioms]. No Karoubi envelope is taken in this
definition: that the category is idempotent complete, and that the envelope
$\Kar(\mathcal P_T)$ is canonically equivalent to it, is recorded with the
other properties of this construction.

*Source note:* the verified Chapter 61 coefficient entries, Section 61.28
([Tag 09BS](https://stacks.math.columbia.edu/tag/09BS)) and Definition
61.28.1 ([Tag 09BT](https://stacks.math.columbia.edu/tag/09BT)), keep a
fixed Noetherian ring $\Lambda$ with an ideal $I$ and define constructible,
lisse and adic lisse $\Lambda$-sheaves on $X_{\Proet}$; Definition 61.29.1
([Tag 09C1](https://stacks.math.columbia.edu/tag/09C1), fetched and quoted)
fixes the category $D_{cons}(X,\Lambda)$ of those $K$ that are derived
complete with respect to $I$ and have
$K\otimes^L_\Lambda\underline{\Lambda/I}$ of constructible cohomology and
locally of finite tor dimension, and Proposition 61.29.7 ([Tag
09C7](https://stacks.math.columbia.edu/tag/09C7), on a Noetherian scheme the
constructible objects are the adic constructible ones) identifies the two
descriptions; all of them keep $\Lambda$ fixed, whereas the form used here
is the filtered colimit of the finite-stage categories $\Dbc(T,E)$ over the
finite extensions $E/\Ql$; the blueprint adds that colimit construction,
with its scalar action and its shift.
