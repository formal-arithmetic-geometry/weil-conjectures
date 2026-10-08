+++
id = "lemma-constructible-of-refines"
kind = "lemma"
title = "Constructibility passes to refinements"
order = 1294
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_refines", "AlgebraicGeometry.Scheme.Stratification.Refines.isFiniteLocallyConstantSheaf_upperStar"]
uses = ["def-constructible-constructible", "def-constructible-finite-locally-constant", "def-constructible-refines", "def-constructible-stratification", "lemma-constructible-immersion-independence", "prop-constructible-pullback"]
+++
Let $(\iota_k\colon Z_k\to X)_k$ be a stratification with all
$\iota_k^*\mathcal F$ finite locally constant, and let
$(\kappa_l\colon W_l\to X)_l$ refine it. Then all $\kappa_l^*\mathcal F$
are finite locally constant.

## Proof

Fix $l$ and choose $k$ with $X'_l\subseteq X_k$. The base change
$\kappa'_l\colon W_l\times_XZ_k\to Z_k$ of $\kappa_l$ is an immersion, and
the composite $\iota_k\circ\kappa'_l\colon W_l\times_XZ_k\to X$ is an
immersion with image $\iota_k(\iota_k^{-1}(X'_l))=X'_l$, the same image as
$\kappa_l$. Its pullback of $\mathcal F$ is
$\kappa_l'^*\iota_k^*\mathcal F$, finite locally constant by
[prop-constructible-pullback] (its lemmas for locally constant and
finite sheaves). By [lemma-constructible-immersion-independence],
$\kappa_l^*\mathcal F$ is finite locally constant.
