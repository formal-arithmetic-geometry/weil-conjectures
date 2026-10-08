+++
id = "def-trf-iterated-weil-map"
kind = "definition"
title = "Iterated Weil isomorphism and scheme-Frobenius map"
order = 2295
uses = ["def-trf-scheme-frobenius", "def-trf-strict-weil-complex", "prop-trf-scheme-galois-comparison"]
+++
Let $(K,\varphi)\in D^b_{ctf,\mathrm W}(X,A)$ under the conventions of
[def-trf-strict-weil-complex]. For $m\in\mathbf Z_{\geq1}$ define
the iterated Weil isomorphism

$$
\varphi^{[m]}:Lg_\gamma^{m*}K\xrightarrow{\ \sim\ }K,
\qquad
\varphi^{[m]}=\varphi\circ Lg_\gamma^*\varphi\circ\cdots\circ
L(g_\gamma^{m-1})^*\varphi,
$$

and, with $\kappa^{(m)}$ of [prop-trf-scheme-galois-comparison],
the scheme-Frobenius map

$$
u_m=\varphi^{[m]}\circ\kappa^{(m)}_K:
L\Phi^m{}^*K\xrightarrow{\ \sim\ }K.
$$

The cocycle identity satisfied by the $\varphi^{[m]}$ is
[lem-trf-iterated-weil-cocycle].
