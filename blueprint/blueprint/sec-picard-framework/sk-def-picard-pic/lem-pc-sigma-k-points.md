+++
id = "lem-pc-sigma-k-points"
kind = "lemma"
title = "$\\operatorname{Pic}_{X/k,\\sigma}$ at $T=\\operatorname{Spec}(k)$"
order = 807
uses = ["def-pc-base-change", "def-sc-picard-group", "lem-pc-pic-of-field"]
+++
Let $k$ be a field, $X$ a scheme over $k$ and $\sigma\in X(k)$. Then

$$
\operatorname{Pic}_{X/k,\sigma}(k)=\operatorname{Pic}(X)
$$

canonically.

## Proof

For $T=\operatorname{Spec}(k)$, the morphism $\sigma_T$ is the original
$\sigma:\operatorname{Spec}(k)\to X$ and $\sigma^*=i_\sigma^*:\operatorname{Pic}(X)\to\operatorname{Pic}(\operatorname{Spec} k)$
sends an invertible module to its fibre (the pullback along the closed
immersion $\sigma$), a $1$-dimensional $k$-vector space, hence trivial
by [lem-pc-pic-of-field]: the map is the zero map. Therefore the
kernel of $\sigma^*$ is all of $\operatorname{Pic}(X)$.
