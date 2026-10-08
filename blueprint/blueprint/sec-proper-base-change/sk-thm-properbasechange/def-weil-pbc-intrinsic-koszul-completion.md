+++
id = "def-weil-pbc-intrinsic-koszul-completion"
kind = "definition"
title = "Intrinsic Koszul completion"
order = 1257
uses = ["def-weil-pbc-adic-derived-inverse-limit"]
+++
Let

$$
Q_m:=K(\Lambda;f_1^m,\ldots,f_r^m)
$$

be the Koszul complex in degrees $[-r,0]$. Its map $Q_{m+1}\to Q_m$ is
the tensor product, over $j$, of the two-term chain maps whose degree-zero
component is the identity and whose degree-minus-one component is
multiplication by $f_j$. Define

$$
K^{\wedge,\mathrm{Kos}}:=
R\varprojlim_m(K\otimes^L_\Lambda Q_m).
$$

The augmentations $\Lambda\to Q_m$ give
$\kappa_K:K\to K^{\wedge,\mathrm{Kos}}$. Call $K$ intrinsically derived
$I$-complete when $\kappa_K$ is an isomorphism; below, ``derived
$I$-complete'' always means this intrinsic condition.
