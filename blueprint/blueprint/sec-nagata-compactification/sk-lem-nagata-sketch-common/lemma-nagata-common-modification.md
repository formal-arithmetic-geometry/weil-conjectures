+++
id = "lemma-nagata-common-modification"
kind = "lemma"
title = "Properties of the common modification, [stacks-project]"
order = 240
lean = ["AlgebraicGeometry.nonempty_commonModification"]
uses = ["cor-nagata-blowup-product-common-refinement", "def-nagata-admissible-blowup", "def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-blowup-product-comparison", "def-nagata-blowup-product-domination-maps", "def-nagata-common-modification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-effective-cartier-ideal", "def-nagata-elimination-indeterminacy", "def-nagata-extended-admissible-blowup", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-invertible-ideal", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-strict-transform", "lem-weil-pbc-closed-immersion-from-composite", "lemma-nagata-admissible-blowup-comp", "lemma-nagata-affine-blowup-complement", "lemma-nagata-blowup-proper", "lemma-nagata-elimination-indeterminacy", "lemma-nagata-extend-admissible-blowup", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-ideal-unit-off-support", "lemma-nagata-localization-ideal-pow", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-product-ideal-common-blowup", "lemma-nagata-proper-to-separated-target", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-partial-section", "lemma-nagata-separated-two-open-cover", "lemma-nagata-strict-transform-closure-characterization", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-product-ideal", "thm-nagata-blowup-universal-property", "thm-nagata-global-blowup-proper", "thm-nagata-strict-transform-is-blowup"]
+++
Each constructed map $X'_i\to X_i$ is a $U$-admissible blow-up. Each
$X'_i\to\mathsf{CM}(X_1,X_2;U)$ is an open immersion, their two copies of
$U$ agree, and $\mathsf{CM}(X_1,X_2;U)$ is separated and of finite type
over $S$.

## Proof

Apply Stacks Project, Tag 0F3X (Lemma 38.33.4), with the qcqs base $S$,
the common quasi-compact open $U$, and the separated finite-type
morphisms $X_i\to S$. The two input maps are open immersions and are
identified over $U$, so the hypotheses of that theorem are exactly the
hypotheses of the present construction. Its scheme-theoretic image
$X_{12}\subseteq X_1\times_SX_2$ is the object named in
[def-nagata-common-modification]; the two projections are the partial
sections used by
[lemma-nagata-scheme-image-partial-section]. The theorem first
principalizes the two projection ideals and then takes their product
center, which is the map $X'_{12}\to X_{12}$ supplied by
[lemma-nagata-product-ideal-common-blowup]. Its strict-transform
comparison gives $X'_{12}\subseteq X'_i$ as an open subscheme, with both
restrictions identified with $U$; this is the extension step recorded by
[lemma-nagata-extend-admissible-blowup]. Consequently the two open
immersions glue along exactly $X'_{12}$, not merely along their underlying
topological intersection. The graph of this overlap is a closed immersion
because $X'_2\to S$ is separated. The composite
$X'_{12}\to X_1\times_SX_2$ is proper, and the product map from
$X'_1\times_SX'_2$ to $X_1\times_SX_2$ is separated; hence the graph map
is proper by
[lemma-nagata-proper-to-separated-target]. It is therefore closed,
so the two-open diagonal criterion
[lemma-nagata-separated-two-open-cover] proves that the glued scheme
is separated. The same theorem gives finite type, and the composition
statement
[lemma-nagata-admissible-blowup-comp] shows that each projection is a
$U$-admissible blow-up.
