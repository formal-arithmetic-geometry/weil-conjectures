+++
id = "prop-constructible-open-closed"
kind = "theorem"
title = "Open–closed criterion"
order = 1537
lean = ["AlgebraicGeometry.Scheme.Stratification.openClosed", "AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_upperStar"]
tags = ["latex:proposition"]
uses = ["def-constructible-constructible", "def-constructible-finite-locally-constant", "def-constructible-stratification", "lemma-constructible-iso-invariance", "prop-constructible-pullback"]
+++
A sheaf $\mathcal F\in\shv{\et X}$ is constructible if and only if
$j^*\mathcal F$ and $i^*\mathcal F$ are constructible.

## Proof

``Only if'' is [prop-constructible-pullback]. Conversely let
$(\kappa_l\colon W_l\to U)_{l<m}$ and $(\lambda_k\colon V_k\to Z)_{k<n}$ be
stratifications witnessing the constructibility of $j^*\mathcal F$ and
$i^*\mathcal F$. The family of the $j\circ\kappa_l$ and the
$i\circ\lambda_k$ is a stratification of $X$ with $m+n$ strata: each
composite is an immersion; the images $j(U_l)$ are locally closed in $X$,
being locally closed in the open $U$; the images $i(Z_k)$ are locally
closed in $X$, being locally closed in the closed $Z$; and the images are
pairwise disjoint and cover $X$ because the $U_l$ partition $U$, the $Z_k$
partition $Z$, and $X=U\sqcup Z$. Finally
$(j\circ\kappa_l)^*\mathcal F\cong\kappa_l^*j^*\mathcal F$ and
$(i\circ\lambda_k)^*\mathcal F\cong\lambda_k^*i^*\mathcal F$ are finite
locally constant by construction and [lemma-constructible-iso-invariance].
