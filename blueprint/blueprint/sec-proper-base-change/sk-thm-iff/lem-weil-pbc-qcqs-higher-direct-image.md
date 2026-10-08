+++
id = "lem-weil-pbc-qcqs-higher-direct-image"
kind = "lemma"
title = "Higher direct images for quasi-compact quasi-separated morphisms"
order = 1071
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-etale-sum-extension", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-etale-restriction-injectives", "prop-weil-pbc-cohomology-resolution-independent", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $u:U\to V$ be a quasi-compact and quasi-separated morphism
[def-weil-pbc-scheme-conventions] of schemes and let $F$ be an etale abelian
sheaf on $U$. Then for every $q\geq0$ the sheaf $R^qu_*F$ of
[def-weil-pbc-direct-image] is the sheafification of the presheaf on the
small etale site [def-weil-pbc-etale-site] of $V$

$$
 W\longmapsto H^q(W\times_VU,F|)
 \qquad(W\to V\text{ etale}),
$$

and on $\Dplus(U_{\Et})$ the derived direct image $Ru_*$ is computed in each
degree by the same description, applied to a K-injective resolution
[def-weil-pbc-kinjective-resolutions].

## Proof

Choose a K-injective resolution $F\to I^\bullet$ of the sheaf
[def-weil-pbc-etale-sheaves] $F$, which exists by
[prop-weil-pbc-kinjective-resolutions-exist]. By
[def-weil-pbc-direct-image] one has $Ru_*F=u_*I^\bullet$, so $R^qu_*F$ is the
$q$-th cohomology sheaf of the complex of sheaves $u_*I^\bullet$. For an
etale $W\to V$ the definition of the direct image gives
$(u_*I^\bullet)(W)=I^\bullet(W\times_VU)$, so the presheaf underlying
$u_*I^\bullet$ assigns to $W$ the complex $\Gamma(W\times_VU,I^\bullet)$;
restriction to the etale $U$-scheme $W\times_VU$ preserves K-injective
complexes, because this restriction functor is exact and has the exact left
adjoint given by extension by zero of
[def-weil-pbc-etale-sum-extension] (injective sheaves being preserved by
[lem-weil-pbc-etale-restriction-injectives], and exact functors with an exact
left adjoint preserving K-injective complexes by the K-injective formalism,
Stacks Project, Lemma 13.31.9, Tag
[08BJ](https://stacks.math.columbia.edu/tag/08BJ)), so the $q$-th cohomology
of that complex is $H^q(W\times_VU,F|)$, the cohomology groups of
[def-weil-pbc-etale-cohomology] being independent of the chosen K-injective
resolution by [prop-weil-pbc-cohomology-resolution-independent]. The presheaf
$W\mapsto H^q(W\times_VU,F|)$ on the small etale site
[def-weil-pbc-etale-site] of $V$ therefore has sheafification equal to the
$q$-th cohomology sheaf of $u_*I^\bullet$, because sheafification is exact
(Stacks Project, Lemma 7.10.15, Tag
[00WJ](https://stacks.math.columbia.edu/tag/00WJ)) and so commutes with the
formation of cohomology of a complex of presheaves; this is the first
assertion. Applying the same computation in every degree to a K-injective
resolution of a bounded-below complex $K\in\Dplus(U_{\Et})$ in place of $F$,
which is legitimate by [def-weil-pbc-kinjective-resolutions], gives the
second assertion.
