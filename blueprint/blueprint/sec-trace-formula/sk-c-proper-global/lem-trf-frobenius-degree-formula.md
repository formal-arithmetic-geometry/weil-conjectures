+++
id = "lem-trf-frobenius-degree-formula"
kind = "lemma"
title = "Degree formula for the local Frobenius"
order = 2345
uses = ["def-trf-frobenius-operators", "def-trf-iterated-weil-map", "lem-trf-iterated-weil-cocycle", "lem-trf-local-frobenius-conjugacy", "prop-trf-scheme-galois-comparison", "prop-trf-trace-formal-laws"]
+++
Let $x\in|X_0|$ be a closed point with degree
$d_x=[\kappa(x):\Fq]$, let $m$ be divisible by $d_x$, let
$x_m\in X_0(\mathbf F_{q^{d_x}})$ be a point above $x$, and put
$F_x=F_{x_m,d_x}$, the *one-circuit local Frobenius* (well
defined up to conjugation by
[lem-trf-local-frobenius-conjugacy]). Then for every
$y\in X_0(\mathbf F_{q^m})$ above $x$,

$$
\operatorname{tr}_A\bigl(F_{y,m}\mid K_{\bar y}\bigr)
=
\operatorname{tr}_A\bigl(F_x^{\,m/d_x}\mid K_{\bar x}\bigr)
$$

in $A$.

## Proof

*Step 1: iteration at one lift.* Let $\bar x$ be the geometric
point of the lift $x_m$, and suppose first that
$m=r\cdot d_x$. For a fixed point $\bar z$ of $\Phi^d$ the
transport $\tau_{z,d}$ of [def-trf-frobenius-operators] is the
canonical identification $K_{\bar z}\cong K_{g_\gamma^d\bar z}\cong K_{\bar z}$ of [prop-trf-scheme-galois-comparison] and the
fixed-point property (the same two identifications and the universal
homeomorphism invariance used in the proof of
[lem-trf-local-frobenius-conjugacy]); the same holds for
$\tau_{z,m}$, and the composite identification for $m=rd$ is the
$r$-fold iteration of the one for $d$ (the functoriality of the
pullback under $g_\gamma^{d}$-iterates, i.e. $g_\gamma^{m}=g_\gamma^{d}\circ\cdots\circ g_\gamma^{d}$). Hence,
with the iterated Weil isomorphisms $\varphi^{[m]}$ of
[def-trf-iterated-weil-map],

$$
\begin{aligned}
F_{z,m}
&=\varphi^{[m]}_{\bar z}\circ\tau_{z,m}
=\varphi^{[d]}_{\bar z}\circ
Lg_\gamma^{d*}\bigl(\varphi^{[(r-1)d]}\bigr)_{\bar z}
\circ\tau_{z,d}\circ\tau_{z,(r-1)d}\\
&=\bigl(\varphi^{[d]}_{\bar z}\circ\tau_{z,d}\bigr)
\circ\bigl(\varphi^{[(r-1)d]}_{\bar z}\circ\tau_{z,(r-1)d}\bigr)
=F_{z,d}\circ F_{z,(r-1)d},
\end{aligned}
$$

where the second equality is the cocycle identity
$\varphi^{[rd]}=\varphi^{[d]}\circ Lg_\gamma^{d*}\varphi^{[(r-1)d]}$
of [lem-trf-iterated-weil-cocycle] together with the naturality of the
canonical stalk identifications (the two ways around the fixed-point
identifications agree, exactly as in the proof of
[lem-trf-local-frobenius-conjugacy], (3)); induction on $r$
gives

$$
F_{z,m}=F_{z,d}^{\,r}
$$

as endomorphisms of $K_{\bar z}$.

*Step 2: changing the lift.* For a general
$y\in X_0(\mathbf F_{q^m})$ above $x$, let
$\bar y=\bar z_i=g_\gamma^i(\bar x)$ ($i$ well defined modulo
$d_x$) and let $T_i:K_{\bar y}\xrightarrow{\sim}K_{\bar x}$ be the
canonical transport of
[lem-trf-local-frobenius-conjugacy], (2). By the conjugacy part
(3) of [lem-trf-local-frobenius-conjugacy] and Step 1,

$$
F_{y,m}=T_i^{-1}F_{z,m}T_i=T_i^{-1}F_{z,d}^{\,r}T_i
=\bigl(T_i^{-1}F_{z,d}T_i\bigr)^{r},
$$

and by the same conjugacy $T_i^{-1}F_{z,d}T_i=F_{x_m,d_x}$ (the
one-circuit operator at the lift $x_m$); this holds for every
$y$ above $x$, so

$$
\operatorname{tr}_A(F_{y,m}\mid K_{\bar y})
=\operatorname{tr}_A\bigl(F_{x_m,d_x}^{\,r}\mid K_{\bar x}\bigr),
$$

the traces being equal because the conjugating isomorphisms are
isomorphisms of the perfect complexes
([prop-trf-trace-formal-laws], (1)), and
$K_{\bar y}\in D^b_{\mathrm{fin}}(A)$. This is the displayed
identity with $r=m/d_x$.
