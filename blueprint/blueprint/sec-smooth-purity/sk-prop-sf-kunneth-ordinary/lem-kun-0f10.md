+++
id = "lem-kun-0f10"
kind = "lemma"
title = "Finite cohomological dimension of finite-type morphisms"
order = 1731
uses = ["def-kun-cd", "def-kun-separably-closed", "def-weil-pbc-scheme-conventions", "lem-kun-cd-sep-closed-point"]
+++
Let $K$ be a field and let $f:X\to Y$ be a morphism between
schemes of finite type over $K$.

1. **(1)** $\kuncd(f)<\infty$.
1. **(2)** If $K$ is separably
closed, then $\kuncd(X)<\infty$ for every scheme $X$ of finite type
over $K$.

Clause (1) and clause (2) are the classical finiteness of the
cohomological dimension of a scheme of finite type over a field, which
this manuscript already imports elsewhere: the finiteness chain of
the constructibility chapter uses it in [sbc-thm-finiteness-finite-type], and
the Jacobian chapter proves the curve case in
lem:sc-cohomological-dimension, so that the curve and proper
instances are internal to the blueprint. The affine bound
$\kuncd(X)\le\kuncd(K)+\kundim X$ for affine $X$ of finite type over
$K$, which is Tag [0F0V](https://stacks.math.columbia.edu/tag/0F0V)
of the Stacks Project, is not needed in this chapter.
(*Source:* Stacks Project, Lemma 59.96.2,
[Tag `0F10`](https://stacks.math.columbia.edu/tag/0F10), in
Section 59.96 (finite cohomological dimension): clause (1) is assertion
(1) of that lemma, and clause (2) is
its assertion (2) — which assumes $\kuncd(K)<\infty$ — combined with
[lem-kun-cd-sep-closed-point], where the cohomological dimension of a
separably closed point is computed to be $0$.) In the Stacks Project the proof uses the induction principle of
Cohomology of Schemes, Lemma 30.4.1,
[Tag `08DR`](https://stacks.math.columbia.edu/tag/08DR),
with the affine cases Lemma 59.95.8,
[Tag `0F0X`](https://stacks.math.columbia.edu/tag/0F0X), for
clause (1) and Proposition 59.95.6,
[Tag `0F0V`](https://stacks.math.columbia.edu/tag/0F0V), for
clause (2), together with the Mayer–Vietoris sequences Lemma 59.50.2,
[Tag `0EYK`](https://stacks.math.columbia.edu/tag/0EYK), and
Lemma 59.50.1, [Tag
`0A50`](https://stacks.math.columbia.edu/tag/0A50).

## Proof

This is the recorded classical input named in the statement, Stacks Project, Tag [0F10](https://stacks.math.columbia.edu/tag/0F10): a morphism of schemes of finite type over a field has finite cohomological dimension, and over a separably closed field every such scheme does. In the Stacks Project the proof uses the induction principle of Cohomology of Schemes, Lemma 30.4.1 ([Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)) with the affine cases of Tags [0F0X](https://stacks.math.columbia.edu/tag/0F0X) and [0F0V](https://stacks.math.columbia.edu/tag/0F0V), and the Mayer–Vietoris sequences of Tags [0EYK](https://stacks.math.columbia.edu/tag/0EYK) and [0A50](https://stacks.math.columbia.edu/tag/0A50). The curve and proper instances are internal to the blueprint, as recorded in the statement; no separate proof of the general case is given.
