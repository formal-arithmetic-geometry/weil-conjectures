+++
id = "prop-nagata-affine-blowup-chart-cover"
kind = "theorem"
title = "Finite affine chart cover"
order = 89
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.iSup_opensRange_blowupι_eq_top"]
tags = ["latex:proposition"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-rees-graded"]
+++
If $I=(f_0,\ldots,f_r)$, the affine opens

$$
\operatorname{Spec}(A[I/f_i])
$$

form a finite open cover of
$\operatorname{Bl}_I(\operatorname{Spec}A)$.

## Proof

The opens $D_+(f_it)$ cover by
[lemma-nagata-rees-generators-cover-proj]. Replace each one by the
affine spectrum supplied by [prop-nagata-affine-blowup-chart]. The
compatibility of the open embeddings with the structure map is part of that
chart isomorphism.
