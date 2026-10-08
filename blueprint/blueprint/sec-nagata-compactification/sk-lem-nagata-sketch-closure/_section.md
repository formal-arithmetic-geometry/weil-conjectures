+++
id = "sk-lem-nagata-sketch-closure"
kind = "section"
title = "Scheme-theoretic closure and compactification"
order = 63
uses = ["sk-def-nagata-sketch-data"]
lean = ["AlgebraicGeometry.Scheme.Hom.image", "AlgebraicGeometry.Compactification.ofIsImmersion", "AlgebraicGeometry.Compactification.denseRefinement", "AlgebraicGeometry.Compactification.baseChange"]
+++
*Lemma (sketch).*

For a quasi-compact, quasi-separated map $h:T\to Y$, its
scheme-theoretic image $\SIm(h)$ is the smallest closed subscheme of $Y$
through which $h$ factors. It commutes with restriction to an open of $Y$.
Consequently, a quasi-compact immersion into a proper $S$-scheme gives a
compactification by taking its scheme-theoretic image. In particular,
compactifications admit dense refinements, and closed subschemes of a
compactifiable $S$-scheme are compactifiable. Compactifications are
preserved by base change.

## Proof

The ideal is $\ker(\mathcal O_Y\to h_*\mathcal O_T)$; localization on
affine opens gives its restriction property. An immersion is closed in
some open of its target, so its image factor identifies $T$ with an open
of $\SIm(h)$. This image is closed in the proper ambient scheme, hence
proper over $S$. Apply this first to $X\to\overline X$, and then to
$Z\hookrightarrow X\hookrightarrow\overline X$. Properness and
quasi-compact open immersions are stable under base change.

Uses: [sk-def-nagata-sketch-data]
