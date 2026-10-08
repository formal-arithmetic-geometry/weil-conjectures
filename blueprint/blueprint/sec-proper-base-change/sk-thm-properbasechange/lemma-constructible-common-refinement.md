+++
id = "lemma-constructible-common-refinement"
kind = "lemma"
title = "Common refinement"
order = 1293
lean = ["AlgebraicGeometry.Scheme.Stratification.exists_refines", "AlgebraicGeometry.Scheme.Stratification.inter"]
uses = ["def-constructible-refines", "def-constructible-stratification"]
+++
Two stratifications $(\iota_k\colon Z_k\to X)_{k<n}$ and
$(\kappa_l\colon W_l\to X)_{l<m}$ of a scheme $X$ have a common refinement.

## Proof

Index the pairs $(k,l)$ by $k+nl<nm$. The intersections $X_k\cap X'_l$ are
locally closed (an intersection of two locally closed sets is locally
closed), pairwise disjoint, and cover $X$. Take as scheme on the stratum
$X_k\cap X'_l$ the fibre product $Z_k\times_XW_l$ with the immersion
$Z_k\times_XW_l\to X$; it is an immersion, as a composite of the base
change of $\kappa_l$ with $\iota_k$, and its image is
$\iota_k(\iota_k^{-1}(X'_l))=X_k\cap X'_l$. This stratification refines
both given ones.
