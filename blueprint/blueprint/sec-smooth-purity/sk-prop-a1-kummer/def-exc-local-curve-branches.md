+++
id = "def-exc-local-curve-branches"
kind = "definition"
title = "The normalization algebra of local curve branches"
order = 1917
uses = ["def-fin-normalization-extension", "def-sc-normalization"]
+++
For a reduced one-dimensional Noetherian local ring $R$,
let $\mathfrak p_1,\ldots,\mathfrak p_t$ be its minimal
primes. Put

$$
Q(R)=\prod_{a=1}^t\operatorname{Frac}(R/\mathfrak p_a),
\qquad
B(R)=\prod_{a=1}^t\overline{(R/\mathfrak p_a)}^{\,
\operatorname{Frac}(R/\mathfrak p_a)}.
$$

The factors are the integral closures used in
[def-sc-normalization], [def-fin-normalization-extension].
The map $R\to B(R)$ is the product of the quotient maps
followed by the inclusions in these integral closures.
This defines the branch algebra without assuming its
finiteness or a decomposition into local rings.
