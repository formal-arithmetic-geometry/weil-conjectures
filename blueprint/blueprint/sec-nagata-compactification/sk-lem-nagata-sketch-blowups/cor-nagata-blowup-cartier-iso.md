+++
id = "cor-nagata-blowup-cartier-iso"
kind = "theorem"
title = "Blow-up of an effective Cartier center"
order = 112
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupMap_of_isInvertible"]
tags = ["latex:corollary"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-effective-cartier-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-invertible-ideal", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "thm-nagata-blowup-universal-property"]
+++
Let $X$ be a scheme. If $\mathcal I$ is an invertible ideal on $X$, then
$b_{X,\mathcal I}$ is an isomorphism.

## Proof

The identity of $X$ lifts to the blow-up by the universal property. Compose
this lift with the blow-up map in both orders and use uniqueness.
