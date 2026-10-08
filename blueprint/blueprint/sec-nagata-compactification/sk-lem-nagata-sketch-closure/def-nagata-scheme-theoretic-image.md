+++
id = "def-nagata-scheme-theoretic-image"
kind = "definition"
title = "Scheme-theoretic image"
order = 65
lean = ["AlgebraicGeometry.Scheme.Hom.image"]
uses = ["def-weil-pbc-scheme-conventions", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $g\colon T\to Y$ be a morphism. Define
$\operatorname{SIm}(g)$ to mean the Mathlib scheme-theoretic image
`Scheme.Hom.image g`, with inclusion $g_{\mathrm{im}}$ and factor map
$g^{\mathrm{im}}$ supplied by
[lemma-nagata-scheme-image-ideal-qc]. Whenever a later argument needs
quasi-compactness, it must state that hypothesis explicitly.

## Detailed form

For a morphism $u:W\to X$ of schemes, the *scheme-theoretic image* of $u$ is
the largest closed subscheme $X'$ of $X$ through which $u$ factors, i.e. the
closed subscheme defined by $\ker(\mathcal O_X\to u_*\mathcal O_W)$. A
subscheme $W\subseteq X$ is *scheme-theoretically dense* if its
scheme-theoretic image in $X$ is $X$ itself. The scheme-theoretic closure of a
locally closed subscheme is the scheme-theoretic image of its immersion.
