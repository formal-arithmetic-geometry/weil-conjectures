+++
id = "lem-zl-complex-extension"
kind = "lemma"
title = "Extension stability of complex weights"
order = 2812
uses = ["def-weil-complex-weights", "def-weil-derived-cohomology-sheaves", "def-weil-frobenius-module-weights", "def-weil-pbc-qbar-category", "def-weil-punctual-weights", "lem-a1-extension-bounds", "lem-a1-mixed-direct-summand", "lem-a1-subquotient-extension-bounds", "lem-sp-long-exact-of-triangle"]
+++
Let $K'\to K\to K''\to K'[1]$ be a distinguished triangle in the
constructible $\Qlb$-Weil categories of
[def-weil-pbc-qbar-category]. If $K'$ and $K''$ belong to

$$
D_{\le w}(X_0):=\{K:\Wt_{\iota,\leq w}(K)\}
$$

in the sense of [def-weil-complex-weights], then so does $K$.

## Proof

The long exact sequence of [lem-sp-long-exact-of-triangle] for the
distinguished triangle, read in the cohomology sheaves of
[def-weil-derived-cohomology-sheaves], contains, for every $j$,
the exact sequence

$$
\mathcal H^j(K')\to\mathcal H^j(K)\to\mathcal H^j(K'')\to
\mathcal H^{j+1}(K')\to\cdots .
$$

By [def-weil-complex-weights]-plus-[def-weil-punctual-weights],
$\mathcal H^j(K')$ and $\mathcal H^j(K'')$ are $\iota$-mixed of weights
at most $w+j$. The exact sequence exhibits $\mathcal H^j(K)$ as an
extension of a subobject of $\mathcal H^j(K'')$ by a quotient of
$\mathcal H^j(K')$: the image of $\mathcal H^j(K')\to\mathcal H^j(K)$
is a Weil quotient sheaf of $\mathcal H^j(K')$, and the image of
$\mathcal H^j(K)\to\mathcal H^j(K'')$ is a Weil subsheaf of
$\mathcal H^j(K'')$ (all maps in the long exact sequence are morphisms
of Weil sheaves). By the sheaf-level stability of mixedness under
subsheaves, quotients and extensions,
[lem-a1-mixed-direct-summand] (1) and (2), both are $\iota$-mixed of
weights at most $w+j$, and hence so is $\mathcal H^j(K)$. (The
Frobenius-module bounds [lem-a1-subquotient-extension-bounds],
[lem-a1-extension-bounds] of [def-weil-frobenius-module-weights] are the
stalkwise shadow of this.) Since $j$ was arbitrary, $K\in D_{\le w}(X_0)$,
which is [def-weil-complex-weights].
