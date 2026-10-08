+++
id = "prop-nagata-affine-blowup-chart"
kind = "theorem"
title = "Affine chart identification"
order = 34
lean = ["AlgebraicGeometry.AffineBlowup.chart"]
tags = ["latex:proposition"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-homogeneous-away-to-chart-injective", "lemma-nagata-homogeneous-away-to-chart-surjective", "prop-nagata-rees-graded"]
+++
The constructed morphism $\chi_a$ is an isomorphism over
$\operatorname{Spec}(A)$.

## Proof

The ring map $\theta_a$ is bijective by the two cited lemmas. The induced
affine morphism is therefore an isomorphism. Compatibility with the
structure morphism is checked on the image of every $r\in A$.
