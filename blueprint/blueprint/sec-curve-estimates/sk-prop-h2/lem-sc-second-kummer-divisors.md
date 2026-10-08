+++
id = "lem-sc-second-kummer-divisors"
kind = "lemma"
title = "Second Kummer cohomology of a curve"
order = 983
uses = ["def-sc-curves", "def-sc-kummer-sequence", "def-sc-picard-group", "def-weil-pbc-etale-cohomology", "lem-sc-brauer-zero-all-curves", "lem-sc-divisor-class-curve", "lem-sc-function-field-cd-one", "lem-sc-generic-kummer-residues", "lem-sc-h1-gm-pic", "lem-sc-kummer-les", "lem-sc-smooth-normal", "thm-sp-grothendieck"]
+++
Let $C$ be a curve over algebraically closed $k$ in the sense of
[def-sc-curves]. It may be singular, non-reduced, disconnected or
have zero-dimensional components. Let $n>0$ be invertible in $k$.
Then

$$
H^2(C,\mu_n)\simeq\operatorname{Pic}(C)/n,
$$

where $\mu_n$, the Picard group, and cohomology are as in
[def-sc-kummer-sequence], [def-sc-picard-group], [def-weil-pbc-etale-cohomology].
The isomorphism is induced by the coboundary of the Kummer sequence,
$\operatorname{Pic}(C)=H^1(C,\mathbf G_m)\to H^2(C,\mu_n)$
([lem-sc-h1-gm-pic]). In particular $H^2(C_{\Et},\mathbf G_m)=0$
for every such $C$ ([lem-sc-brauer-zero-all-curves]).

## Proof

By [lem-sc-brauer-zero-all-curves], $H^2(C_{\Et},\mathbf G_m)=0$.
This is exactly the hypothesis of [lem-sc-kummer-les]. That lemma
identifies $H^2(C,\mu_n)$ with
$\operatorname{coker}(n:\operatorname{Pic}(C)\to\operatorname{Pic}(C))
=\operatorname{Pic}(C)/n$, via the coboundary of the Kummer sequence
and [lem-sc-h1-gm-pic].

*Explicit form for smooth $C$.* When $C$ is a smooth separated
connected curve, the same group can be computed at the generic point
without using the Brauer group. This also describes the isomorphism
by divisors.
Write $K=k(C)$.
Normality ([lem-sc-smooth-normal]) gives
$\eta_*\mu_n=\mu_n$: on every normal etale test object an
$n$-th root of unity in its rational functions is integral,
and therefore regular. The low-degree exact sequence of
[thm-sp-grothendieck] is

$$
H^1(K,\mu_n)\longrightarrow H^0(C,R^1\eta_*\mu_n)
\longrightarrow H^2(C,\mu_n)\longrightarrow H^2(K,\mu_n).
$$

The last term is zero by [lem-sc-function-field-cd-one].
The first two terms and their arrow are

$$
K^\times/K^{\times n}\longrightarrow
\bigoplus_{x\in C_{\rm cl}}\mathbf Z/n,\qquad
f\longmapsto (v_x(f)\bmod n)_x,
$$

by [lem-sc-generic-kummer-residues].
The cokernel is the divisor group modulo principal divisors
and $n$ times the divisor group. This is
$\operatorname{Pic}(C)/n$ by [lem-sc-divisor-class-curve].
