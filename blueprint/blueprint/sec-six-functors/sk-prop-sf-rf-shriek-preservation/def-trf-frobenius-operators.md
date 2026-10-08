+++
id = "def-trf-frobenius-operators"
kind = "definition"
title = "Global and local geometric Frobenius operators"
order = 2090
uses = ["def-trf-coefficient-conventions", "def-weil-derived-cohomology-sheaves", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-global-geometric-frobenius", "def-weil-ordinary-compact-cohomology", "prop-trf-scheme-galois-comparison", "thm-trf-frobenius-fixed-points", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Fix the global finite-field datum
and the coefficient
conventions, and let $(K,\varphi)\in D^b_{ctf,\mathrm W}(X,A)$.

1. The *$m$-th iterate of the global geometric Frobenius* is
$$
F_{c,K}^{\,m}:
R\Gamma_c(X,K)\longrightarrow R\Gamma_c(X,K),
$$
the composite of the canonical
direct-image identification
with the compact-support
global geometric
Frobenius action constructed in the trace-formula chapter applied to
$\varphi^{[m]}$. Its description as
$R\Gamma_c(X,\varphi^{[m]})\circ g_{\gamma,c}^{m,*}$, where
$g_{\gamma,c}^{m,*}$ is the compact-support base-change isomorphism
along the automorphism $g_\gamma^m$, is
`lem-trf-frobenius-operator-compact-description` of the trace-formula chapter. It is the
endomorphism of the
compact-support
cohomology $H_c^i(X,K)$ in the finite coefficient stage.
1. For a point $x\in X_0(\mathbf F_{q^m})$ with geometric point
$\bar x:\Spec k\to X$ lying over $x$, define the *local
geometric Frobenius*
$$
F_{x,m}:K_{\bar x}\longrightarrow K_{\bar x},
\qquad
F_{x,m}=\varphi^{[m]}_{\bar x}\circ\tau_{x,m},
$$
where $\tau_{x,m}:K_{\bar x}\xrightarrow{\ \sim\ } \bigl(Lg_\gamma^{m*}K\bigr)_{\bar x}$ is the canonical stalk
transport and $K_{\bar x}=L\bar x^*\operatorname{For}(K)$ is the
stalk complex of the
derived pullback.
The dependence of $F_{x,m}$ on the lift and, through a closed point
below, on the degree, is recorded in
[lem-trf-local-frobenius-conjugacy] and
[lem-trf-frobenius-degree-formula]; that the transport
$\tau_{x,m}$ is defined for every point
$x\in X_0(\mathbf F_{q^m})$ is the fixed-point statement
[thm-trf-frobenius-fixed-points].

*Recorded in advance* from chapter *The trace formula* of the source.
