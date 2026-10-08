+++
id = "lemma-nagata-closed-subscheme-fp-system"
kind = "lemma"
title = "Properties of the closed-subscheme system, [stacks-project]"
order = 388
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_of_mem", "AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_fgSubDiagram_map", "AlgebraicGeometry.Scheme.IdealSheafData.isLimitFgSubCone", "AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_fgSub_subschemeι"]
uses = ["def-nagata-closed-subscheme-fp-system", "def-nagata-extended-ideal", "def-nagata-noetherian-inverse-system", "def-nagata-scheme-image-comparison", "lemma-nagata-scheme-image-universal", "lemma-nagata-scheme-theoretic-closure-minimal", "prop-nagata-noetherian-inverse-system"]
+++
Every $X_\alpha\hookrightarrow Y$ is of finite presentation, all
transitions are closed immersions, and the canonical map
$X\to\varprojlim_\alpha X_\alpha$ is an isomorphism.

## Proof

Finite type of $\mathcal I_\alpha$ is equivalent to finite presentation of
$X_\alpha\hookrightarrow Y$, and each transition $X_\beta\to X_\alpha$ is a
closed immersion because its composite with the closed immersion
$X_\alpha\hookrightarrow Y$ is the closed immersion
$X_\beta\hookrightarrow Y$.

For the limit, the content is that $\mathcal I$ is the union of its finite
type subideals. We prove this by absolute Noetherian approximation of $Y$
rather than by the quasi-coherent extension theorem
([Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)): write
$Y=\varprojlim_j Y_j$ with $Y_j$ Noetherian and affine transition maps. An
affine open of $Y$ is the preimage of an affine open $V$ of some stage $Y_j$,
and a section of $\mathcal I$ over it comes from a section over $V$ at a
later stage; so we may assume it comes from $Y_j$. The ideal
$\mathcal K_j\subseteq\mathcal O_{Y_j}$ cutting out the scheme-theoretic
image of $X$ in $Y_j$ is of finite type, because a closed immersion into a
Noetherian scheme is of finite presentation, and its inverse image
$\mathcal K_j\cdot\mathcal O_Y$ is a finite type subideal of $\mathcal I$
containing the given section.

Finally, if $T$ is any scheme with compatible maps $T\to X_\alpha$, then the
induced map $T\to Y$ has $\mathcal I_\alpha$ in its kernel ideal for every
$\alpha$, hence has $\mathcal I$ in its kernel ideal by the exhaustion just
proved; so it factors uniquely through $X=V(\mathcal I)$ by the universal
property of closed immersions. This is exactly the limit property.
