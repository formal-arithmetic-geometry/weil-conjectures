+++
id = "prop-nagata-dense-refinement"
kind = "theorem"
title = "Properties of the dense-refinement construction"
order = 82
lean = ["AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_denseRefinement_i"]
tags = ["latex:proposition"]
uses = ["def-nagata-compactification", "def-nagata-dense-compactification", "def-nagata-dense-refinement", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-scheme-image-ideal-qc"]
+++
The object $\mathsf{Dense}(C)$ is a scheme-theoretically dense
compactification of the same morphism as $C$.

## Proof

The induced map from $X$ is a quasi-compact open immersion and is
scheme-theoretically dense by
[lemma-nagata-immersion-open-in-scheme-image]. The new ambient scheme
is closed in $\overline X$, so it remains proper over $S$. Finally, if
$p\colon\overline X\to S$ is the original structural map, then

$$
j^{\mathrm{im}};j_{\mathrm{im}};p
=j;p=f
$$

by `Scheme.Hom.toImage_imageι`; hence the refined factorization has
the same composite as $C$.
