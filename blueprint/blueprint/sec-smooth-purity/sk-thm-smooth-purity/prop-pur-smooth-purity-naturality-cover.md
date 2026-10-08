+++
id = "prop-pur-smooth-purity-naturality-cover"
kind = "theorem"
title = "Naturality and independence of the smooth purity map"
order = 2015
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-pur-smooth-purity-map", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "thm-pur-affine-line-orientation", "thm-pur-cohomological-smoothness", "thm-pur-diagonal-dualizing-object", "thm-pur-dnc-invariance", "thm-pur-finite-coefficient-smooth-purity", "thm-pur-rank-one-local-calculation"]
+++
In the situation of [thm-pur-finite-coefficient-smooth-purity],
the smooth purity map $\gamma_{f,K}$ of
[def-pur-smooth-purity-map] is natural in $K$, and it is
independent of the choices made in its construction.

## Proof

Naturality in $K$ is the naturality of the tensor formula
[thm-pur-cohomological-smoothness], of the twist
isomorphisms [def-coefficient-twists-detailed], and of the
identification of [thm-pur-diagonal-dualizing-object] (in the
object and in the morphism, all steps of the construction of
[def-pur-smooth-purity-map] being canonical derived
transformations).
The independence of the choices: the construction contains no
choices at all – the identification of
[thm-pur-diagonal-dualizing-object] is the unique one normalized
on the standard pairs and compatible with base change and etale
localization ([thm-pur-dnc-invariance]), the tensor formula and
the twist isomorphisms are canonical, and the normalization of the
fundamental class is the single one of the Kummer boundary of the
coordinate ([thm-pur-affine-line-orientation] and
[thm-pur-rank-one-local-calculation]).
