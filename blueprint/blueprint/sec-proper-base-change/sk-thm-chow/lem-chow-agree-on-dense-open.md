+++
id = "lem-chow-agree-on-dense-open"
kind = "lemma"
title = "Two morphisms agreeing on a scheme-theoretically dense open"
order = 1056
lean = ["AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant"]
uses = ["def-nagata-dense-compactification", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-closed-immersion-products"]
+++
Let $T$ and $Y$ be schemes over $S$ with $Y\to S$ separated, let
$a,b\colon T\to Y$ be morphisms of $S$-schemes and let $V\subseteq T$ be a
scheme-theoretically dense open subscheme with $a|_V=b|_V$. Then $a=b$.

## Proof

This is 01RH. Concretely, the equaliser of $a$ and $b$ is the
base change of the diagonal $Y\to Y\times_S Y$ along
$(a,b)\colon T\to Y\times_S Y$, hence a closed subscheme of $T$ because
$Y\to S$ is separated; it contains $V$, which is scheme-theoretically dense, so
it is all of $T$.

## Detailed form

Let $Z$ be a scheme, $U\subseteq Z$ a scheme-theoretically dense
([def-nagata-scheme-theoretic-image]) open subscheme, and $f,g:Z\to
X$ two morphisms into a separated scheme $X$ with $f|_U=g|_U$. Then $f=g$.

## Proof

The equalizer $E$ of $f$ and $g$ is the inverse image of the diagonal of $X$
under $(f,g):Z\to X\times X$; as $X$ is separated, the diagonal is a closed
immersion, and closed immersions are stable under base change, so $E\subseteq
Z$ is a closed subscheme. It contains $U$, which is scheme-theoretically dense
in $Z$ by [def-nagata-scheme-theoretic-image]; hence $E=Z$, i.e.
$f=g$. (This is Stacks Project, Morphisms, Lemma 29.7.10, Tag
[01RH](https://stacks.math.columbia.edu/tag/01RH).)
