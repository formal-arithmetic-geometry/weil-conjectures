+++
id = "lem-sc-normalization-properties"
kind = "lemma"
title = "Properties of the normalization"
order = 919
uses = ["def-sc-normalization", "lem-sc-normalization-exists", "lem-sc-normalization-over-normal-locus", "lem-sc-normalized-curve-smooth"]
+++
Let $X$ be an integral scheme of finite type over a field $k$
and $\nu:X^{\nu}\to X$ its normalization in $k(X)$
([def-sc-normalization]).

1. **(a)** $\nu$ is finite, surjective and birational; if $X$ is
proper then $X^{\nu}$ is proper; $\dim X^{\nu}=\dim X$.
1. **(b)** $\nu$ is an isomorphism over the open set of normal
points of $X$: for every open $U\subseteq X$ which is normal, the
induced morphism $X^{\nu}\times_XU\to U$ is an isomorphism.
1. **(c)** If $\dim X=1$ and $k$ is perfect, then
$X^{\nu}$ is smooth over $k$.

## Proof

Part (a) is [lem-sc-normalization-exists]; part (b) is
[lem-sc-normalization-over-normal-locus]; part (c) is
[lem-sc-normalized-curve-smooth].
