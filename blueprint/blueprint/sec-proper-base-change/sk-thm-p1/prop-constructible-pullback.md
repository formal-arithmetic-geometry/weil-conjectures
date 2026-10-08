+++
id = "prop-constructible-pullback"
kind = "theorem"
title = "Pullback of constructible sheaves"
order = 1165
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf.upperStar", "AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.upperStar"]
tags = ["latex:proposition"]
uses = ["def-constructible-constructible", "def-constructible-finite", "def-constructible-finite-locally-constant", "def-constructible-locally-constant", "def-constructible-stratification", "lemma-constructible-iso-invariance", "lemma-constructible-pullback-finite", "lemma-constructible-pullback-locally-constant", "lemma-constructible-pullback-stratification"]
+++
Let $g\colon Y\to X$ be a morphism and let $\mathcal F\in\shv{\et X}$ be
constructible. Then $g^*\mathcal F$ is constructible. In particular
constructibility is preserved by restriction to an open, to a closed
subscheme, and to any locally closed subscheme.

## Proof

Let $(\iota_k\colon Z_k\to X)_k$ be a stratification of $X$ with all
$\iota_k^*\mathcal F$ finite locally constant, and let
$(\iota'_k\colon Z_k\times_XY\to Y)_k$ be its pullback
([lemma-constructible-pullback-stratification]), with projections
$g_k\colon Z_k\times_XY\to Z_k$. Since $\iota_k\circ g_k=g\circ\iota'_k$
and pullback is functorial up to natural isomorphism,
$\iota_k'^*g^*\mathcal F\cong g_k^*\iota_k^*\mathcal F$, which is finite
locally constant by
[lemma-constructible-pullback-locally-constant], [lemma-constructible-pullback-finite]
and [lemma-constructible-iso-invariance].
