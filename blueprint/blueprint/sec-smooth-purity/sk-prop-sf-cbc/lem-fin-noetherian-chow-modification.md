+++
id = "lem-fin-noetherian-chow-modification"
kind = "lemma"
title = "A projective modification of a reduced proper scheme"
order = 1620
uses = ["cor-chow-lemma-proper", "def-pc-projective-morphism", "def-weil-pbc-scheme-conventions", "lem-chow-affine-immersion", "lem-chow-closed-model", "lem-chow-glue", "lem-chow-graph", "lem-chow-preimage", "lemma-nagata-dense-affine-cover-exists", "thm-chow-lemma"]
+++
Let $S$ be affine Noetherian and $X\to S$
proper, with $X$ reduced.
There are a proper map $\pi:Y\to X$ and a dense open $U\subset X$
such that $\pi^{-1}(U)\to U$ is an isomorphism and $Y\to S$ is
projective.

## Proof

Apply [lemma-nagata-dense-affine-cover-exists] to obtain finitely many
affine opens $U_i$ containing all generic points of $X$.
Their intersection $U$ is dense and is scheme-theoretically dense
in each $U_i$: a function on a reduced affine scheme vanishing
at all its generic points belongs to all minimal primes and is zero.
By [lem-chow-affine-immersion], embed $U_i$
in a projective space over $S$, and take its closed model $Z_i$
by [lem-chow-closed-model].
The closure $W$ of the diagonal copy of $U$ in $\prod_i Z_i$
is the model of [lem-chow-graph].
Put $V_i=W\times_{Z_i}U_i$ and $Y=\bigcup_iV_i$.
The projections glue to $\pi:Y\to X$ by
[lem-chow-glue].
The fibre calculation of [lem-chow-preimage]
and [thm-chow-lemma]
show that $\pi$ is proper and is an isomorphism over $U$.
Finally [cor-chow-lemma-proper]
makes the resulting immersion $Y\to\mathbf P^N_S$ closed.
All hypotheses of this construction hold on the given Noetherian
scheme; no descent of an arbitrary proper morphism to a
Noetherian approximation is needed.
