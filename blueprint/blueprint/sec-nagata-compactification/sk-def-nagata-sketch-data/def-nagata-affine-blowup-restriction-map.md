+++
id = "def-nagata-affine-blowup-restriction-map"
kind = "definition"
title = "Affine blow-up restriction morphism"
order = 45
lean = ["AlgebraicGeometry.AffineBlowup.hom"]
uses = ["def-nagata-affine-blowup", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-piece-membership", "prop-nagata-rees-graded", "prop-nagata-relative-proj-functoriality"]
+++
Define

$$
r_s\colon
\operatorname{Bl}_{IA_s}(\operatorname{Spec}A_s)
\longrightarrow
\operatorname{Bl}_I(\operatorname{Spec}A)
\times_{\operatorname{Spec}A}\operatorname{Spec}A_s
$$

by applying the relative-Proj morphism of
[prop-nagata-relative-proj-functoriality] to $\rho_s$ and the
canonical degree-zero identifications.
