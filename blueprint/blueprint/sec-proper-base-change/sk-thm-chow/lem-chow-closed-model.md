+++
id = "lem-chow-closed-model"
kind = "lemma"
title = "Closed model of a quasi-compact immersion"
order = 1054
lean = ["AlgebraicGeometry.ProperClosedModel", "AlgebraicGeometry.nonempty_properClosedModel"]
uses = ["def-nagata-affine-proj", "def-nagata-dense-compactification", "def-nagata-projective-space-base-change", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-chow-affine-immersion", "lem-weil-pbc-closed-immersion-proper", "lem-weil-pbc-proper-composition", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
Let $S$ be a scheme and let $j\colon V\to\mathbf P^n_S$ be a quasi-compact
immersion. Let $Z\subseteq\mathbf P^n_S$ be the scheme-theoretic image of $j$.
Then $Z$ is a closed subscheme of $\mathbf P^n_S$, the induced morphism
$V\to Z$ is an open immersion identifying $V$ with a scheme-theoretically dense
open subscheme of $Z$, and $Z\to S$ is proper.

The formalisation packages this data as a structure
`ProperClosedModel`, in the case in which it is used below: $S$ is
noetherian and $g\colon V\to S$ is locally of finite type with $V$ affine, so
that $j$ is supplied by [lem-chow-affine-immersion] and is automatically
quasi-compact because $V$ is then noetherian.

## Proof

The first two assertions are 01RG applied to the quasi-compact
immersion $j$. For the last one, $\mathbf P^n_S\to S$ is proper by
01WC, a closed immersion is proper by 01W5, and
a composition of proper morphisms is proper; hence $Z\to S$ is proper.

## Detailed form

Let $Y$ be affine and let $j:U\hookrightarrow\mathbf P^n_Y$ be an immersion of
a quasi-compact scheme $U$. Let $Z\subseteq\mathbf P^n_Y$ be the
scheme-theoretic closure of the image of $j$, in the sense of
[def-nagata-scheme-theoretic-image]. Then $j$ factors as

$$
 U\hookrightarrow Z\hookrightarrow\mathbf P^n_Y,
$$

where $U\hookrightarrow Z$ is a scheme-theoretically dense open immersion and
$Z\hookrightarrow\mathbf P^n_Y$ is the closed immersion; in particular $Z\to
Y$ is proper, as the composite of the closed immersion
$Z\hookrightarrow\mathbf P^n_Y$ with the proper $\mathbf P^n_Y\to Y$.

## Proof

By [def-nagata-scheme-theoretic-image], $Z$ is the largest closed
subscheme of $\mathbf P^n_Y$ through which $j$ factors, so the factorization
into the closed immersion $Z\hookrightarrow\mathbf P^n_Y$ and the induced
morphism $U\to Z$ exists. The latter is an open immersion with $U$
scheme-theoretically dense in $Z$: this is exactly Stacks Project, Morphisms,
Lemma 29.7.7 (Tag [01RG](https://stacks.math.columbia.edu/tag/01RG)), applied
to the immersion $j$ (which is quasi-compact because $U$ is quasi-compact),
whose conclusion is that the scheme-theoretic image $Z$ of an immersion
contains $U$ as a scheme-theoretically dense open subscheme (and
topologically dense). Finally: a closed immersion is proper; the
projective-space morphism is proper (Stacks Project, Morphisms, Lemma 29.44.5,
Tag [01WC](https://stacks.math.columbia.edu/tag/01WC), applied to $\mathbf
P^n_Y\to Y$); composites of proper morphisms are proper. Hence $Z\to Y$ is the
composite of two proper morphisms, hence proper.
