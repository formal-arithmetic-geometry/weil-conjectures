+++
id = "sbc-lem-affine-space-smooth"
kind = "lemma"
title = "Affine space is smooth"
order = 1378
uses = ["def-sbc-affine-space", "def-sbc-smooth-morphisms"]
+++
For every scheme $S$ and every $n\geq0$, the projection
$\mathbf A^n_S\to S$ of [def-sbc-affine-space] is
smooth of
relative dimension $n$.
(*Stacks Project: the ring map $R\to R[x_1,\dots,x_n]$ is standard
smooth,
[Algebra, Definition
10.137.5](https://stacks.math.columbia.edu/tag/00T6) and
[Lemma 10.137.6](https://stacks.math.columbia.edu/tag/00T7), so
the projection is smooth in the sense of
[Definition 29.35.1](https://stacks.math.columbia.edu/tag/01V5),
hence also in the sense of [def-sbc-smooth-morphisms] by
[Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6); and
$\Omega_{\mathbf A^n_S/S}$ is finite locally free of rank $n$, which by
[Lemma 29.35.12](https://stacks.math.columbia.edu/tag/02G1) is
$\dim_x(\mathbf A^n_{\kappa(f(x))})$ at every point $x$, so that the
projection has relative dimension $n$ in the sense of
[def-sbc-smooth-morphisms].*)

## Proof

This is the recorded classical input named in the statement: the polynomial ring is standard smooth over the base (Stacks Project, Algebra, Definition 10.137.5 and Lemma 10.137.6, [Tag 00T6](https://stacks.math.columbia.edu/tag/00T6), [Tag 00T7](https://stacks.math.columbia.edu/tag/00T7)), the two notions of smoothness agree (Lemma 37.11.7, [Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)), and the module of differentials is finite locally free of rank n, which by Lemma 29.35.12 ([Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)) computes the relative dimension. No separate proof is given.
