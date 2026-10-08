+++
id = "lemma-nagata-chart-generator-regular"
kind = "lemma"
title = "Regularity of the chart generator"
order = 94
lean = ["AlgebraicGeometry.AffineBlowup.isRegular_awayAlgebraMap"]
uses = ["def-nagata-blowup-chart-ring", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
Multiplication by $a$ on $A[I/a]$ is injective.

## Proof

The chart algebra is a subring of $A_a$. The image of $a$ is a unit in
$A_a$, hence multiplication by it is injective on the subring.
