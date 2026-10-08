+++
id = "prop-weil-pbc-descent-functors"
kind = "theorem"
title = "Descent of coefficient-compatible functors"
order = 1312
uses = ["def-weil-pbc-finite-stage-pair-category", "def-weil-pbc-qbar-category", "prop-weil-pbc-scalar-extension"]
tags = ["latex:proposition"]
+++
Let $\Phi_E:\mathcal C_E(T)\to\mathcal C_E(S)$ be exact functors and let
$$
 \beta_{F/E}:T^S_{F/E}\Phi_E
 \xrightarrow{\sim}\Phi_FT^T_{F/E}
$$
be exact natural isomorphisms satisfying the unit, associator, and shift
equations of [prop-weil-pbc-scalar-extension]. Then they induce an exact
functor $\Phi:\mathcal P_T\to\mathcal P_S$. On a representative
$u:T^T_{M/E}K\to T^T_{M/F}L$, its value is represented by
$$
 T^S_{M/E}\Phi_EK\xrightarrow{\beta_{M/E}}
 \Phi_MT^T_{M/E}K\xrightarrow{\Phi_M(u)}
 \Phi_MT^T_{M/F}L\xrightarrow{\beta_{M/F}^{-1}}
 T^S_{M/F}\Phi_FL.
$$
This functor is, by [def-weil-pbc-qbar-category], already a functor on the
$\Qlb$ coefficient categories $\Dbc(T,\Qlb)=\mathcal P_T$ and
$\Dbc(S,\Qlb)=\mathcal P_S$. Compatible natural transformations and their
equations descend by the same formula.

In particular, the scalar-compatible families $(Rf_{*,E})_E$ and
$(Lg_E^*)_E$ descend to exact functors on $\Qlb$ coefficient categories, and
the finite-stage exchange maps descend to a natural transformation.

*Source note:* no Stacks Project entry states this descent of functors: the
ledger's verified entries contain no filtered-colimit-of-categories
statement — the nearest, the Chapter 61 coefficient entries 09BS, 09BT, 09C1
and 09C7, work with one fixed Noetherian coefficient ring — and the
blueprint adds the descent of scalar-compatible exact functors and of their
natural transformations to the $\Qlb$ coefficient categories, together with
the descended direct images, pullbacks and exchange maps. The closest
descent statements in Stacks, each fetched and quoted, are the universal
properties of a localization and of a Verdier quotient: Lemma 13.5.7 ([Tag
05R7](https://stacks.math.columbia.edu/tag/05R7), an exact functor out of
$\mathcal D$ that inverts the multiplicative system factors uniquely and
exactly through $S^{-1}\mathcal D$) and Lemma 13.6.8 ([Tag
05RJ](https://stacks.math.columbia.edu/tag/05RJ), the same for the quotient
$\mathcal D/\mathcal B$ by a full triangulated subcategory), with Definition
13.6.1 ([Tag 05RB](https://stacks.math.columbia.edu/tag/05RB), saturated,
i.e. thick, triangulated subcategory) and Definition 13.6.7 ([Tag
05RI](https://stacks.math.columbia.edu/tag/05RI),
$\mathcal D/\mathcal B=S^{-1}\mathcal D$). Difference: a localization or
quotient inverts a multiplicative system inside one category and its
factorization needs no further data, whereas $\mathcal P_T$ is a filtered
colimit of categories and the functors descend with the explicit
$\beta$-isomorphisms of [prop-weil-pbc-scalar-extension].

## Proof

Define $\Phi(E,K)=(E,\Phi_EK)$ on objects and, on a representative $(M,u)$,
by the displayed composite in $\mathcal C_M(S)$. The value is independent of
$M$: for $M\subset N$ the $\beta$-isomorphisms transport the composite for
$u$ to the composite for $u_N$, using the unit and associator equations of
[prop-weil-pbc-scalar-extension] which the $\beta$'s satisfy; equivalent
representatives give equal composites at the witnessing stage by those
equations, so $\Phi$ is well defined on the morphisms of
[def-weil-pbc-finite-stage-pair-category]. It is additive, the composites
being exact functors and exact natural isomorphisms of exact natural
transformations, and exact (finite-stage exactness of the $\Phi_E$ and the
$T$'s makes the composite exact on distinguished triangles); natural
transformations and their equations descend by that formula by the
equivariance with the $\beta$'s. By [def-weil-pbc-qbar-category] this is
already the descent to the $\Qlb$ coefficient categories
($\Dbc(T,\Qlb)=\mathcal P_T$ and $\Dbc(S,\Qlb)=\mathcal P_S$); no extension
to an envelope is needed. The families $(Rf_{*,E})_E$ and $(Lg_E^*)_E$ carry
the scalar-extension isomorphisms of [prop-weil-pbc-scalar-extension] as the
data $\beta$, so they descend to exact functors on the $\Qlb$ coefficient
categories, and the finite-stage exchange maps, being compatible with scalar
extension, descend to a natural transformation.
