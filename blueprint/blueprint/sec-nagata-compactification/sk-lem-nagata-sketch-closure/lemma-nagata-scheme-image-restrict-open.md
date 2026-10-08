+++
id = "lemma-nagata-scheme-image-restrict-open"
kind = "lemma"
title = "Restriction of a scheme-theoretic image to an open target"
order = 85
lean = ["AlgebraicGeometry.Scheme.Hom.ker_morphismRestrict"]
uses = ["def-nagata-extended-ideal", "def-nagata-scheme-theoretic-image", "lemma-nagata-dense-flat-pullback"]
+++
Let $g\colon T\to Y$ be quasi-compact and quasi-separated, let
$W\subseteq Y$ be open, let $T_W=T\times_YW$, and let
$g_W\colon T_W\to W$ be the base change of $g$. Then

$$
\operatorname{SIm}(g_W)
\cong\operatorname{SIm}(g)\times_YW
$$

as closed subschemes of $W$, compatibly with their inclusions into $W$.

## Proof

On an affine open $V=\operatorname{Spec}(A)\subseteq Y$, the image ideal is
the kernel of
$A\to\Gamma(T\times_YV,\mathcal O)$. On every principal open
$D(s)\subseteq V\cap W$,
[lemma-nagata-dense-flat-pullback] identifies the image
kernel of the restricted morphism with the localization of this ideal.
The declaration
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`
identifies that localized ideal with the comap of the original image ideal,
and `Scheme.IdealSheafData.comapIso` identifies the closed
subscheme it defines with the fibre product. Functoriality under further
localization makes these affine isomorphisms agree on overlaps. They glue
to the displayed canonical isomorphism, and the construction from equal
ideal sheaves makes it compatible with the two inclusions into $W$.
