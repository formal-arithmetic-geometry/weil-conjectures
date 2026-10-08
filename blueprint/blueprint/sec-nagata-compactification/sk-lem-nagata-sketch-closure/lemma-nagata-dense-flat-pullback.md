+++
id = "lemma-nagata-dense-flat-pullback"
kind = "lemma"
title = "Flat base change of scheme-theoretic images and dense pullbacks"
order = 84
lean = ["AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback", "AlgebraicGeometry.Scheme.Hom.ker_pullback_snd"]
uses = ["def-nagata-dense-compactification", "def-nagata-extended-ideal", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $h\colon U\to X$ be quasi-compact and quasi-separated with
scheme-theoretic image $X$, and let
$q\colon P\to X$ be flat. Then

$$
U\times_XP\longrightarrow P
$$

has scheme-theoretic image $P$.

## Proof

By [lemma-nagata-dense-flat-pullback], the scheme-theoretic
image after pullback is canonically the pullback of the scheme-theoretic
image of $h$. By hypothesis that image is $X$, and its pullback along
$P\to X$ is the identity closed subscheme of $P$. Thus the base-changed
morphism is scheme-theoretically dense in $P$.

## Localization of the affine image kernel

Let $A$ be a ring, let $T\to\operatorname{Spec}(A)$ be quasi-compact and
quasi-separated, and let $s\in A$. Put

$$
I=\ker\bigl(A\longrightarrow\Gamma(T,\mathcal O_T)\bigr).
$$

If $T_s=T\times_{\operatorname{Spec}(A)}\operatorname{Spec}(A_s)$, then

$$
\ker\bigl(A_s\longrightarrow\Gamma(T_s,\mathcal O_{T_s})\bigr)=IA_s.
$$

This equality is functorial under further localization.

*Proof.*
Choose a finite affine cover $(T_i)$ of $T$. Quasi-separatedness makes
each $T_i\cap T_j$ quasi-compact, so choose a finite affine refinement of
every such intersection. The sheaf equalizer for this finite covering
computes $\Gamma(T,\mathcal O_T)$ from finite products of the coordinate
rings of the selected affine opens and their finite affine refinements.
Localizing this equalizer at $s$ is exact, commutes with its finite
products, and replaces every selected affine by its inverse image in
$T_s$. It therefore computes $\Gamma(T_s,\mathcal O_{T_s})$. Taking the
kernel of the structural map gives $IA_s$. Repeating the same construction
after a second localization gives the stated functoriality.

## Flat base change of the affine image kernel

Let $A\to B$ be flat, let $T\to\operatorname{Spec}(A)$ be quasi-compact
and quasi-separated, and put

$$
I=\ker\bigl(A\longrightarrow\Gamma(T,\mathcal O_T)\bigr).
$$

For $T_B=T\times_{\operatorname{Spec}(A)}\operatorname{Spec}(B)$ one has

$$
\ker\bigl(B\longrightarrow\Gamma(T_B,\mathcal O_{T_B})\bigr)=IB.
$$

The equality is natural in the flat algebra $B$ and commutes with
localization on $B$.

*Proof.*
Use the finite affine cover and finite affine refinements from
[lemma-nagata-dense-flat-pullback]. Tensor its finite
sheaf equalizer with $B$. Flatness makes tensoring exact, and tensoring
commutes with the finite products in this diagram. The resulting affine
coordinate rings are precisely those of the base-changed cover of $T_B$,
so the resulting equalizer computes $\Gamma(T_B,\mathcal O_{T_B})$.
Exactness identifies the kernel of the base-changed structural map with
$I\otimes_A B$, whose image in $B$ is $IB$. Naturality follows from the
naturality of tensor product, and compatibility with localization is
[lemma-nagata-dense-flat-pullback] applied over $B$.

## Flat base change of a scheme-theoretic image (Stacks Project)

Let $g\colon T\to Y$ be quasi-compact and quasi-separated and let
$q\colon Y'\to Y$ be flat. For the base change
$g'\colon T\times_YY'\to Y'$ one has a canonical isomorphism

$$
\operatorname{SIm}(g')
\cong\operatorname{SIm}(g)\times_YY'
$$

of closed subschemes of $Y'$.

*Proof.*
Work over an affine open $V=\operatorname{Spec}(A)\subseteq Y$ and an
affine open $V'=\operatorname{Spec}(B)\subseteq q^{-1}(V)$. The ring map
$A\to B$ is flat. Apply
[lemma-nagata-dense-flat-pullback] to
$T\times_YV\to\operatorname{Spec}(A)$. It identifies the ideal of the
image after base change to $V'$ with the extension to $B$ of the original
image ideal. The latter is exactly the ideal defining
$\operatorname{SIm}(g)\times_YV'$ under the closed-subscheme pullback
isomorphism. Naturality and localization compatibility in
[lemma-nagata-dense-flat-pullback] show that these affine
identifications agree on all overlaps. Gluing gives the displayed
canonical isomorphism of closed subschemes of $Y'$. This is the
finite-affine-cover proof of Stacks Project, Tag 081I
(Lemma 29.26.16), with $f=q$ and $g$ the morphism in the present statement.
