+++
id = "def-fd-trace-function"
kind = "definition"
title = "Trace function of a Weil complex"
order = 2689
lean = ["AlgebraicGeometry.WeilSheaf.traceFunction"]
uses = ["def-weil-local-frobenius-trace", "def-weil-pbc-qbar-category"]
+++
For a Weil complex $K$ on a separated finite-type $k_0$-scheme $X_0$
and an $\mathbf F_{q^n}$-point $x\in X_0(\mathbf F_{q^n})$, the
*trace function* of $K$ at $x$ is

$$
t_K(x)=\operatorname{Tr}\bigl(F_x^{(n)}\mid K_{\bar x}\bigr)
=\sum_{j\in\mathbf Z}(-1)^j\operatorname{Tr}\bigl(F_x^{(n)}\mid\mathcal H^j(K)_{\bar x}\bigr),
$$

computed with the local Frobenius operators of
[def-weil-local-frobenius-trace] in the
$\overline{\mathbf Q}_\ell$-coefficient category of
[def-weil-pbc-qbar-category].
