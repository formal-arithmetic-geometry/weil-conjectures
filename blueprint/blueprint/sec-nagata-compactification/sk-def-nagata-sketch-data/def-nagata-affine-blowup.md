+++
id = "def-nagata-affine-blowup"
kind = "definition"
title = "Affine blow-up"
order = 25
lean = ["AlgebraicGeometry.AffineBlowup"]
uses = ["def-nagata-affine-proj", "def-nagata-rees-algebra", "def-nagata-rees-piece", "prop-nagata-rees-graded"]
+++
For an ideal $I\subseteq A$, define

$$
\operatorname{Bl}_I(\operatorname{Spec}A)
=\operatorname{Proj}(\mathcal R_A(I)).
$$

Its structure morphism is induced by the canonical degree-zero map
$A\to\mathcal R_A(I)_0$.
