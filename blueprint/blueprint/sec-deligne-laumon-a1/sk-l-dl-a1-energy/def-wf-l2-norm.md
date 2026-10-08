+++
id = "def-wf-l2-norm"
kind = "definition"
title = "The $L^2$-weight parameter"
order = 2757
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-pbc-constructible-complexes", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions"]
+++
Let $X_0$ be a smooth geometrically connected affine curve over
$k_0=\mathbf F_q$ (the separated finite-type conventions of
[def-weil-pbc-scheme-conventions]), let $\mathcal F$ be a
constructible Weil complex
in the coefficient category of [def-weil-pbc-qbar-category],
and for $m\ge1$ let

$$
\|f_{\mathcal F}\|_m^2\;:=\;\sum_{y\in X_0(k_m)}
\left|\iota\sum_i(-1)^i
\operatorname{Tr}(F_y^{(m)}\mid\mathcal H^i(\mathcal F)_{\bar y})\right|^2
$$

(the square of the $L^2$-norm of the trace function of the
Frobenius of the $k_m$-basis). The *$L^2$-weight parameter*
of $\mathcal F$ (the $\|\cdot\|$ of the Ch. I route) is

$$
\|\mathcal F\|\;:=\;\sup\Bigl\{\beta\in\mathbf R:\
\limsup_{m\to\infty}\ \frac{\|f_{\mathcal F}\|_m^2}{q^{m(\beta+1)}}>0\Bigr\},
$$

the $\sup$ of the empty set being $-\infty$, the exponent $1$
being $\dim(X_0)$.
