+++
id = "prop-weil-pbc-proetale-constant-exact"
kind = "theorem"
title = "Exactness of the pro-etale inverse image for constant coefficients"
order = 1236
uses = ["def-weil-pbc-inverse-image", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-operations", "def-weil-pbc-proetale-site", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-inverse-image-exact", "prop-weil-pbc-proetale-constant-ring-map"]
tags = ["latex:proposition"]
+++
Let $\Lambda$ be a finite discrete ring, let $u:U\to V$ be a morphism
[def-weil-pbc-scheme-conventions] of schemes, and let the coefficient sheaves
be the constant sheaves $\Lambda_{U,\Proet},\Lambda_{V,\Proet}$ of
[def-weil-pbc-proetale-modules]. Then the module inverse image $u^*$ of
[def-weil-pbc-proetale-operations] is an exact functor on $\Lambda$-module
sheaves.

## Proof

By [def-weil-pbc-proetale-operations] the module inverse image is

$$
 u^*F=u^{-1}F\otimes_{u^{-1}\Lambda_{V,\Proet}}\Lambda_{U,\Proet},
$$

and [prop-weil-pbc-proetale-constant-ring-map] identifies the base ring
$u^{-1}\Lambda_{V,\Proet}$ with $\Lambda_{U,\Proet}$, so that $u^*F\cong
u^{-1}F\otimes_{\Lambda_{U,\Proet}}\Lambda_{U,\Proet}\cong u^{-1}F$,
naturally in $F$. The functor $u^{-1}$ is exact: by
[def-weil-pbc-inverse-image] the presheaf inverse image is computed
sectionwise and has both a left and a right adjoint, so it preserves kernels
and cokernels, and sheafification of presheaves of abelian groups is exact
(Stacks Project, Lemma 7.10.15, Tag
[00WJ](https://stacks.math.columbia.edu/tag/00WJ)); this is the argument of
[prop-weil-pbc-inverse-image-exact] carried out on the small pro-etale site
in place of the small etale site. Hence $u^*$, being naturally isomorphic to
$u^{-1}$, is exact as well.
