+++
id = "prop-trf-frobenius-factorization"
kind = "theorem"
title = "Factorization of the absolute Frobenius"
order = 2072
tags = ["latex:proposition"]
uses = ["def-trf-scheme-frobenius"]
+++
For every $m\in\mathbf Z_{\geq1}$, the absolute $q^m$-power Frobenius
$\operatorname{Fr}^{(q^m)}_X:X\to X$, $a\otimes b\mapsto a^{q^m}\otimes b^{q^m}$, factors as

$$
\operatorname{Fr}^{(q^m)}_X=g_\sigma{}^m\Phi^m=\Phi^mg_\sigma{}^m.
$$

## Proof

By [def-trf-scheme-frobenius] all three morphisms are $k_0$-maps
of the geometric fiber whose affine incarnations are the $q^m$-th power
map on the $A_0$-factor, the $q^m$-th power map on the $\bar k$-factor, or their composition, in either order; thus both composites
equal $\operatorname{Fr}^{(q^m)}_X$.

*Recorded in advance* from chapter *The trace formula* of the source.
