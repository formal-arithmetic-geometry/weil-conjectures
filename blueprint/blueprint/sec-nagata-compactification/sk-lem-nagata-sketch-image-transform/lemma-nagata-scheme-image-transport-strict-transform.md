+++
id = "lemma-nagata-scheme-image-transport-strict-transform"
kind = "lemma"
title = "Scheme-image transport to a strict transform"
order = 232
uses = ["lemma-nagata-scheme-image-affine-saturation", "lemma-nagata-scheme-image-restrict-open", "lemma-nagata-strict-transform-closure-characterization", "prop-nagata-strict-transform-closed-fiber-product", "thm-nagata-global-blowup-complement"]
+++
Let $h\colon T\to X\times_SY$ be quasi-compact, with
first projection factoring through a quasi-compact open $U\subseteq X$.
(The Stacks Project assumes $h$ quasi-separated as well; the formalised
statement drops it, since the kernel ideal sheaf theory used here only needs
quasi-compactness, exactly as recorded for
[lemma-nagata-dense-flat-pullback].)
Let $Z=\operatorname{SIm}(h)$ and let $\pi\colon X'\to X$ be a
$U$-admissible blow-up. Via the canonical identity
$X'\times_XU\cong U$, let $h'$ be the lifted map to $X'\times_SY$. Then

$$
\operatorname{SIm}(h')
\;=\;\operatorname{ST}_{X'/X}(Z)
$$

as closed subschemes of $X'\times_SY$, compatibly with their maps to $X'$.

## Proof

Restriction of scheme-theoretic image to $U\times_SY$ identifies the image
there with the image of $h|_U$ by
[lemma-nagata-scheme-image-restrict-open]. Work on an affine chart of
$X'\times_SY$ on which the pulled-back center has principal equation $a$.
Write its coordinate ring as $C$ and refine the source by affine opens
$\operatorname{Spec}(B_j)$. The image ideal on this chart is
$K=\bigcap_j\ker(C\to B_j)$, so $C/K\to\prod_jB_j$ is injective; the image
of $a$ is a unit in every $B_j$ because $h$ factors through $U$. Applying
[lemma-nagata-scheme-image-affine-saturation] to the product ring
identifies the kernel on this chart with the $a$-saturation of the pulled
back image ideal. By
[prop-nagata-strict-transform-closed-fiber-product] and
[lemma-nagata-strict-transform-closure-characterization], that
quotient is precisely the strict-transform chart. The identifications are
unchanged after localization, so they agree on overlaps and glue to the
claimed global equality.
