+++
id = "thm-trf-grothendieck-lefschetz-finite-ring"
kind = "theorem"
title = "Grothendieck–Lefschetz formula over a finite ring"
order = 2380
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-frobenius-coefficient-morphism", "def-trf-frobenius-operators", "def-trf-iterated-weil-map", "def-weil-compactifications-refinements", "def-weil-finite-field-fiber", "def-weil-pbc-etale-origin-witness", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex", "lem-trf-frobenius-degree-formula", "lem-trf-iterated-weil-cocycle", "lem-trf-local-frobenius-conjugacy", "prop-trf-graph-frobenius-operator", "prop-trf-scheme-galois-comparison", "thm-trf-coefficient-morphism-trace-formula", "thm-trf-frobenius-fixed-points"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and the
coefficient conventions,
$A=A_{E,n}$. Let $X_0$ be a
separated finite-type
$k_0$-scheme, put $X=X_0\times_{k_0}k$, let
$(K,\varphi)\in D^b_{ctf,\mathrm W}(X,A)$ be a
strict Weil complex whose
underlying $K$ has an
explicit etale-origin
witness, and assume
the exceptional-adjoint admissibility
hypotheses of [def-trf-admissibility] for the structure morphism
and the fixed-point base changes, including those on a chosen
compactification
defined over $k_0$. For every integer $m\geq1$,

$$
\boxed{
\operatorname{tr}_A\bigl(F_{c,K}^{\,m}\mid R\Gamma_c(X,K)\bigr)
=
\sum_{y\in X_0(\mathbf F_{q^m})}
\operatorname{tr}_A\bigl(F_{y,m}\mid K_{\bar y}\bigr).}
$$

Equivalently, in the closed-point form,

$$
\operatorname{tr}_A\bigl(F_{c,K}^{\,m}\mid R\Gamma_c(X,K)\bigr)
=
\sum_{\substack{x\in|X_0|\\d_x\mid m}}
d_x\,\operatorname{tr}_A
\bigl(F_x^{\,m/d_x}\mid K_{\bar x}\bigr).
$$

Both sides lie in $A$, and both sums are finite.

## Proof

This is the case $\psi=u_1$ of the coefficient-morphism trace formula
[thm-trf-coefficient-morphism-trace-formula], whose hypotheses are
among those assumed here; that theorem is proved by reduction to curves
(closed subschemes of the affine line, the Weil $!$-pushforward along
the relative Frobenius factorization, and localization), and it uses
no compactification of $X_0$.

The scheme-Frobenius map $u_1=\varphi\circ\kappa_K$ of
[def-trf-iterated-weil-map] is an invertible Frobenius coefficient
morphism of [def-trf-frobenius-coefficient-morphism] (the example there),
and its iterates are the scheme-Frobenius maps $u_m$: both are built by
the same recursion, using the cocycle identity
[lem-trf-iterated-weil-cocycle] for $\varphi^{[m]}$ and the
multiplicativity of $\kappa^{(m)}$ in
[prop-trf-scheme-galois-comparison]. By
[prop-trf-graph-frobenius-operator],
$F_{c,m}(u_1)=T_c(u_m)=F_{c,K}^{\,m}$. For
$y\in X_0(\mathbf F_{q^m})$ the geometric point $\bar y$ is fixed by
$\Phi^m$ ([thm-trf-frobenius-fixed-points]), and the stalk map
$u_{m,\bar y}=\varphi^{[m]}_{\bar y}\circ\kappa^{(m)}_{K,\bar y}$ is the
local geometric Frobenius $F_{y,m}=\varphi^{[m]}_{\bar y}\circ\tau_{y,m}$
of [def-trf-frobenius-operators], since at the fixed point $\kappa^{(m)}$
induces the stalk transport $\tau_{y,m}$
([prop-trf-scheme-galois-comparison]). Substituting into
[thm-trf-coefficient-morphism-trace-formula] gives the boxed formula.
Grouping the rational points above a closed point and applying
[lem-trf-frobenius-degree-formula] and
[lem-trf-local-frobenius-conjugacy] gives the second formula.
