+++
id = "lemma-nagata-reduced-dense-image-schematic"
kind = "lemma"
title = "Dense image into a reduced scheme is schematically dense"
order = 276
lean = ["AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant"]
uses = ["def-nagata-dense-compactification", "def-nagata-scheme-theoretic-image"]
+++
Let $X$ be reduced and let $h\colon U\to X$ be quasi-compact and
quasi-separated with dense topological image. Then the image inclusion
$\operatorname{SIm}(h)\hookrightarrow X$ is an isomorphism.

## Proof

On an affine open $\operatorname{Spec}(A)\subseteq X$, every element of the
kernel ideal defining the scheme-theoretic image vanishes at every point of
a dense subset. It therefore lies in every prime ideal of $A$, hence in
the nilradical. Since $A$ is reduced, the element is zero. The kernel
vanishes on an affine cover, so the image inclusion is an isomorphism.
