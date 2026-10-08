+++
id = "prop-weil-pbc-cohomology-resolution-independent"
kind = "theorem"
title = "Resolution independence of etale cohomology"
order = 1068
uses = ["def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-site", "def-weil-pbc-kinjective-resolutions", "prop-weil-pbc-kinjective-resolutions-exist"]
tags = ["latex:proposition"]
+++
Let $T$ be a scheme and let $F$ be an etale abelian sheaf on the small etale
site [def-weil-pbc-etale-site] of $T$. If $F\to I^\bullet$ and $F\to
J^\bullet$ are two K-injective resolutions
[def-weil-pbc-kinjective-resolutions] of $F$, then for every $q\geq0$ the
groups $\mathcal H^q(\Gamma(T,I^\bullet))$ and $\mathcal
H^q(\Gamma(T,J^\bullet))$ are isomorphic, so the groups $H^q(T_{\Et},F)$ of
[def-weil-pbc-etale-cohomology] are independent of the chosen resolution.

## Proof

By [prop-weil-pbc-kinjective-resolutions-exist] the two K-injective
resolutions of $F$ are chain-homotopy equivalent, so there are chain maps
$I^\bullet\to J^\bullet$ and $J^\bullet\to I^\bullet$ over $F$ whose
composites are homotopic to the identities. The additive functor
$\Gamma(T,-)$ occurring in [def-weil-pbc-etale-cohomology] carries chain maps
to chain maps and preserves homotopies and composites, so
$\Gamma(T,I^\bullet)$ and $\Gamma(T,J^\bullet)$ are chain-homotopy
equivalent complexes of abelian groups. Chain-homotopy equivalent complexes
have isomorphic cohomology in every degree, so $\mathcal
H^q(\Gamma(T,I^\bullet))\cong\mathcal H^q(\Gamma(T,J^\bullet))$ for all $q$.
These cohomology groups are the groups $H^q(T_{\Et},F)$ of
[def-weil-pbc-etale-cohomology], which is therefore independent of the
resolution, the resolutions being those of
[def-weil-pbc-kinjective-resolutions].
