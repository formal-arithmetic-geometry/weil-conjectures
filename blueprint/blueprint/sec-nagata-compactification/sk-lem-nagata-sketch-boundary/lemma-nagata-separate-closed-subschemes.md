+++
id = "lemma-nagata-separate-closed-subschemes"
kind = "lemma"
title = "Properties of the closed-boundary separation blow-up, [stacks-project]"
order = 248
lean = ["AlgebraicGeometry.disjoint_range_strictTransformMap_sup"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-separate-closed-subschemes", "def-nagata-strict-transform", "lemma-nagata-blowup-proper", "lemma-nagata-chart-extended-ideal-principal", "lemma-nagata-extended-ideal-affine-chart", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-separate-closed-data-exists", "lemma-nagata-strict-transform-ambient-closed", "lemma-nagata-strict-transform-closure-characterization", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "thm-nagata-global-blowup-proper"]
+++
The morphism $\mathsf{SepBl}_U(Z_1,Z_2)\to X$ is $U$-admissible, and the
strict transforms of $Z_1$ and $Z_2$ in it are disjoint.

## Proof

The selected center is disjoint from $U_Z$, hence its image in $X$ is
disjoint from $U$. A composite of finite-presentation closed immersions is
finite presentation, so the ambient center is finite presentation and its
blow-up is $U$-admissible. By
[lemma-nagata-strict-transform-ambient-closed], the strict transforms
of $Z_1$ and $Z_2$ in this ambient blow-up agree with their strict
transforms in $\operatorname{Bl}_C(Z)$, which are disjoint by the selected
preparation witness.
