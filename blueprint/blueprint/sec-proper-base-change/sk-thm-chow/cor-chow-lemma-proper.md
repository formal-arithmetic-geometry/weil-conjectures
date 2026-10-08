+++
id = "cor-chow-lemma-proper"
kind = "theorem"
title = "Chow's lemma for proper morphisms"
order = 1062
lean = ["AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace"]
tags = ["latex:corollary"]
uses = ["def-nagata-affine-proj", "def-nagata-dense-compactification", "def-nagata-projective-space-base-change", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-chow-agree-on-dense-open", "lem-chow-closed-model", "lem-chow-glue", "lem-chow-graph", "lem-chow-preimage", "lem-chow-scheme-theoretic-closure", "lem-chow-segre", "lem-chow-tuple-immersion", "lem-weil-pbc-closed-immersion-products", "lem-weil-pbc-proper-composition", "lem-weil-pbc-proper-immersion-closed", "lem-weil-pbc-proper-to-separated", "lemma-nagata-dense-affine-cover-exists", "lemma-nagata-dense-flat-pullback", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-projective-space-base-change-proper", "lemma-nagata-projective-target-local", "lemma-nagata-proper-to-separated-target", "lemma-nagata-scheme-image-ideal-qc", "thm-chow-lemma"]
+++
Let $S$ be a noetherian scheme and let $f\colon X\to S$ be a proper morphism.
Then there are an integer $n\geq0$, a proper surjective morphism
$\pi\colon X'\to X$ and a *closed* immersion
$i\colon X'\to\mathbf P^n_S$ of $S$-schemes; moreover $\pi$ is an isomorphism
over a dense open subscheme of $X$. In particular every proper $S$-scheme is
dominated by a projective $S$-scheme through a proper surjective morphism.

## Proof

A proper morphism is separated and of finite type, so [thm-chow-lemma]
applies and yields $\pi\colon X'\to X$ and an immersion
$i\colon X'\to\mathbf P^n_S$ with the stated properties. Both $f$ and $\pi$
are proper, hence so is $f\circ\pi\colon X'\to S$. Since $\mathbf P^n_S\to S$
is separated, 01W6 shows that $i$ is universally closed; in
particular $i(X')\subseteq\mathbf P^n_S$ is closed, and an immersion with
closed image is a closed immersion by 01IQ. Thus $f\circ\pi$
is the composition of the closed immersion $i$ with the structure morphism
$\mathbf P^n_S\to S$, so $X'$ is projective over $S$.

## Detailed form

In the situation of [thm-chow-lemma], the
composite

$$
 i:X'\hookrightarrow\widetilde X\hookrightarrow Z
 \hookrightarrow\prod_{i=1}^m\mathbf P^{n_i}_Y
 \xrightarrow{\ s\ }\mathbf P^N_Y,\qquad N=\prod_{i=1}^m(n_i+1)-1,
$$

of the open immersion $X'\subseteq\widetilde X$, the closed immersion
$\widetilde X\hookrightarrow Z$ of
[lem-chow-graph], the product of the closed immersions
$Z_i\hookrightarrow\mathbf P^{n_i}_Y$, and the Segre embedding
([lem-chow-segre]) is a closed immersion, and
$f\circ\pi$ equals the composite of $i$ with $\mathbf P^N_Y\to Y$.

## Proof

By [thm-chow-lemma], $\pi$ is proper and
surjective and $\pi^{-1}(U)\xrightarrow{\sim}U$. The composite $i$ is a
composite of the open immersion $X'\subseteq\widetilde X$ with closed
immersions (the closed immersion $\widetilde X\hookrightarrow Z$, the product
of the closed immersions $Z_i\hookrightarrow\mathbf P^{n_i}_Y$, and the Segre
embedding), hence an immersion. Its source $X'$ is proper over $Y$: the
composite of the proper surjective $\pi$ with the proper $f$ is proper; its
target $\mathbf P^N_Y$ is separated over $Y$, so $i$ is proper, and a proper
immersion is a closed immersion. Finally $f\circ\pi$ and the composite of $i$
with $\mathbf P^N_Y\to Y$ are both the structure morphism of the $Y$-scheme
$X'$, since every morphism in the display is a morphism of $Y$-schemes, as in
the last paragraph of the proof of
[thm-chow-lemma].
