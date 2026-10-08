+++
id = "lem-wf-weil-fundamental-representation"
kind = "lemma"
title = "The Weil fundamental representation is a continuous representation"
order = 2501
uses = ["cor-galois-lisse-representations", "def-tw-frobenius-action", "def-wf-fundamental-representation"]
+++
In the situation of [def-wf-fundamental-representation], the formula

$$
\rho(\gamma s^n):=\rho_{\mathrm{geom}}(\gamma)T_s^n
\qquad(\gamma\in\pi_1(X,\bar x),\ n\in\mathbf Z)
$$

defines a continuous group homomorphism
$\rho:W(X_0,\bar x)\to\operatorname{GL}(V)$ with
$\rho|_{\pi_1(X,\bar x)}=\rho_{\mathrm{geom}}$ and
$\rho(s)=T_s$.

## Proof

Every $g\in W(X_0,\bar x)$ has a unique expression $g=\gamma s^n$ with
$\gamma\in\pi_1(X,\bar x)$ and $n\in\mathbf Z$. Indeed, the fibre
product of [def-wf-fundamental-representation] is formed over
$\operatorname{Gal}(k/k_0)$ against the cyclic subgroup
$\langle\Phi_X\rangle$ of [def-tw-frobenius-action]: its
projection to $\langle\Phi_X\rangle\cong\mathbf Z$ is a homomorphism
whose kernel consists of the pairs $(\gamma,1)$ with $\gamma$ in the
kernel of $\pi_1(X_0,\bar x)\to\operatorname{Gal}(k/k_0)$, that is, of
the elements of $\pi_1(X,\bar x)$; so $n$ is determined by $g$ and
then $\gamma=gs^{-n}$. Hence the displayed formula defines a map, and it
extends $\rho_{\mathrm{geom}}$ (case $n=0$) and takes $s$ to
$T_s$ (case $\gamma=1$, $n=1$).

It is a homomorphism: $\rho_{\mathrm{geom}}$ is a homomorphism by the
lisse sheaf–representation equivalence of
[cor-galois-lisse-representations]; the commutation relation
displayed in [def-wf-fundamental-representation] rewrites
$\rho_{\mathrm{geom}}(s^n\gamma s^{-n})$ as
$T_s^n\rho_{\mathrm{geom}}(\gamma)T_s^{-n}$; and
$W(X_0,\bar x)$ multiplies as
$(\gamma s^n)(\gamma's^{n'})=\gamma(s^n\gamma's^{-n})s^{n+n'}$.

For continuity let $g=\gamma_0s^n$ and let $U\subseteq \operatorname{GL}(V)$ be an open neighbourhood of $\rho(g)$. The
subset of $W(X_0,\bar x)$ projecting to the fixed exponent $n$ under
the fibre-product projection to $\langle\Phi_X\rangle\cong\mathbf Z$ is
open in $W(X_0,\bar x)$, and on it the formula
reads $\gamma s^n\mapsto\rho(g)\rho_{\mathrm{geom}}(\gamma_0^{-1}\gamma)$.
By the continuity of $\rho_{\mathrm{geom}}$ of
[cor-galois-lisse-representations] there is an open subgroup
$N\subseteq\pi_1(X,\bar x)$ with
$\rho_{\mathrm{geom}}(N)\subseteq\rho(g)^{-1}U$, and then
$\rho(Ns^n)\subseteq U$.
