+++
id = "lemma-nagata-affine-blowup-top"
kind = "lemma"
title = "Blow-up of the unit ideal"
order = 36
lean = ["AlgebraicGeometry.AffineBlowup.isIso_toSpec_of_eq_top"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-proj", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-chart", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded"]
+++
The blow-up of $\operatorname{Spec}(A)$ in the unit ideal is canonically
isomorphic to $\operatorname{Spec}(A)$ over $\operatorname{Spec}(A)$.

## Proof

The Rees algebra of the unit ideal is $A[t]$. The single standard open
$D_+(t)$ covers Proj, and its chart algebra $A[A/1]$ is $A$.
