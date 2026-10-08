+++
id = "lemma-nagata-immersion-open-in-scheme-image"
kind = "lemma"
title = "[stacks-project]"
order = 73
lean = ["AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact"]
uses = ["def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $g\colon T\to Y$ be a quasi-compact immersion. The constructed map
$g^{\mathrm{im}}\colon T\to\operatorname{SIm}(g)$ is a quasi-compact open
immersion, and its image is topologically and scheme-theoretically dense.

## Proof

Apply the verified instance
`AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact`
to $g$. It gives that
$g^{\mathrm{im}}=\texttt{Scheme.Hom.toImage g}$ is an open immersion.
The verified instance
`AlgebraicGeometry.Scheme.instQuasiCompactToImage` gives
quasi-compactness of the same factor map.
The verified instance
`AlgebraicGeometry.Scheme.instIsDominantToImageOfQuasiCompact` says
that its topological range is
dense. For every affine open $V$ of $Y$, the theorem
`Scheme.Hom.toImage_app_injective` gives injectivity on the
corresponding affine open of $\operatorname{SIm}(g)$ obtained by pulling
$V$ back along the image inclusion. These opens form an affine basis of
$\operatorname{SIm}(g)$, so the sheaf morphism
$\mathcal O_{\operatorname{SIm}(g)}\to (g^{\mathrm{im}})_*\mathcal O_T$ is injective on a basis and hence globally.
Thus the factor map is scheme-theoretically dense, including at boundary
points.
