+++
id = "prop-nagata-affine-blowup-restrict"
kind = "theorem"
title = "Restriction of an affine blow-up"
order = 46
lean = ["AlgebraicGeometry.AffineBlowup.isPullback_hom_of_isLocalization"]
tags = ["latex:proposition"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-localization-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-chart", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "prop-nagata-rees-localization", "prop-nagata-relative-proj-functoriality"]
+++
The constructed morphism $r_s$ is an isomorphism over
$\operatorname{Spec}(A_s)$.

## Proof

By [prop-nagata-rees-localization], the coefficientwise localization
of the Rees algebra is the Rees algebra of $IA_s$. On the standard open
indexed by a homogeneous generator, the induced map is the isomorphism of
degree-zero chart rings from the localization equivalence. These chart
isomorphisms agree on overlaps by the localization cocycle, and therefore
glue to an inverse to $r_s$. The degree-zero piece is $A_s$ on both sides,
so the glued inverse and $r_s$ are morphisms over $\operatorname{Spec}(A_s)$.
