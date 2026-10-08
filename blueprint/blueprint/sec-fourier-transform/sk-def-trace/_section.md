+++
id = "sk-def-trace"
kind = "section"
title = "The trace function, and the classical Fourier transform"
order = 2688
lean = ["AlgebraicGeometry.WeilSheaf.traceFunction"]
uses = ["sk-def-char", "sk-def-fourier-set"]
+++
*Definition (sketch).*

For a Weil complex $K$ on a separated finite-type $k_0$-scheme and an
$\mathbf F_{q^n}$-point $x$,

$$
t_K(x)=\Tr\bigl(F_x^{(n)}\mid K_{\bar x}\bigr)
=\sum_j(-1)^j\Tr\bigl(F_x^{(n)}\mid\mathcal H^j(K)_{\bar x}\bigr),
$$

with the local Frobenius operators of def:weil-local-frobenius-trace.
This is a numerical invariant of $K$; the classical Fourier transform of a
function on $\mathbf F_{q^n}$, $\widehat f(y)=\sum_xf(x)\psi_n(xy)$, is the
model for P8 below. (Blueprint def:fd-trace-function.)

Uses: [sk-def-char], [sk-def-fourier-set]
