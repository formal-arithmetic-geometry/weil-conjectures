+++
id = "lemma-nagata-maximal-isomorphism-open"
kind = "lemma"
title = "Properties of the maximal isomorphism open"
order = 258
lean = ["AlgebraicGeometry.Scheme.Hom.isIso_restrict_maximalIsomorphismOpen"]
uses = ["def-nagata-maximal-isomorphism-open"]
+++
The subset $\operatorname{IsoOpen}(q)$ is open,
$q^{-1}(\operatorname{IsoOpen}(q))\to\operatorname{IsoOpen}(q)$ is an
isomorphism, and every open over which $q$ is an isomorphism is contained in
it.

## Proof

A union of opens is open. On pairwise intersections, the inverses of the
restricted morphisms agree because an inverse to a fixed morphism is unique;
hence the local inverses glue to an inverse over the union. If an open
$W$ has the property that $q^{-1}(W)\to W$ is an isomorphism, then $W$ is
one of the opens in the defining union, and therefore $W\subseteq \operatorname{IsoOpen}(q)$; this is the maximality assertion.
