+++
id = "def-per-support-condition"
kind = "definition"
title = "Support and cosupport conditions"
order = 2738
uses = ["def-trf-dualizing-complex", "def-weil-derived-cohomology-sheaves", "def-weil-pbc-constructible-complexes", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions"]
+++
Let $X$ be a
separated scheme of finite
type over a field $k$, and work in the bounded constructible
$\overline{\mathbf Q}_\ell$-coefficient categories of
[def-weil-pbc-qbar-category] on the etale site of $X$, with the
constructible conventions of
[def-weil-pbc-constructible-complexes] and the cohomology sheaves
$\mathcal H^i$ of [def-weil-derived-cohomology-sheaves]. For
$K\in D^b_c(X,\overline{\mathbf Q}_\ell)$ write

$$
\operatorname{SuppCon}(K)\quad\Longleftrightarrow\quad
\dim\operatorname{Supp}\mathcal H^{-i}(K)\le i\qquad(i\in\mathbf Z),
$$

with the convention that the empty support has dimension $-\infty$, and

$$
\operatorname{CosuppCon}(K)\quad\Longleftrightarrow\quad
\operatorname{SuppCon}\bigl(D_XK\bigr),
$$

where $D_X$ is the Verdier dual of [def-trf-dualizing-complex].
