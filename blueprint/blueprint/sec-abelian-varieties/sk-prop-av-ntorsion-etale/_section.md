+++
id = "sk-prop-av-ntorsion-etale"
kind = "section"
title = "The $n$-torsion of an abelian variety is étale"
lean = ["AlgebraicGeometry.etale_torsionSubgroupScheme"]
order = 587
uses = ["sk-cor-av-commutative", "sk-def-av", "sk-def-av-group-scheme", "sk-def-av-mult-n", "sk-prop-av-connected-order", "sk-prop-av-divisible", "sk-prop-av-divisible-structure", "sk-prop-av-finite-etale-points", "sk-prop-av-isogeny", "sk-prop-av-prime-p-etale"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety of dimension $g$ over an algebraically
closed field $k$ and let $n$ be prime to $\operatorname{char}k$. Then
$A[n]$ is a finite étale group scheme over $k$, the canonical base
change map $A[n](k)\to A[n](k')$ is an isomorphism for every extension
$k\subseteq k'$ of algebraically closed fields, and

$$
A[n](k)\cong(\Z/n\Z)^{2g}.
$$

## Proof

By [sk-prop-av-isogeny], $A[n]$ is a finite flat group scheme of order
$n^{2g}$ over $k$, with $n$ prime to $\operatorname{char}k$; by
[sk-prop-av-prime-p-etale] it is étale, and by
[sk-prop-av-finite-etale-points] $\lvert A[n](k)\rvert=n^{2g}$ and
$A[n](k)\to A[n](k')$ is bijective. For the group structure: $A(k)$
is abelian by [sk-cor-av-commutative] and divisible by
[sk-prop-av-divisible], and for a prime power $\ell^e$ with
$\ell\ne\operatorname{char}k$ the subgroup $A(k)[\ell^e]=A[\ell^e](k)$
has order $\ell^{2ge}$ by the above, so $\lvert A(k)[\ell]\rvert =\ell^{2g}$ and [sk-prop-av-divisible-structure] gives
$A[\ell^e](k)\cong(\Z/\ell^e\Z)^{2g}$. For general
$n=\prod_i\ell_i^{e_i}$ prime to $\operatorname{char}k$ the subgroup
schemes $A[\ell_i^{e_i}]$ have coprime orders, so
$A[n]=\prod_iA[\ell_i^{e_i}]$ and the Chinese remainder theorem gives
$A[n](k)\cong(\Z/n\Z)^{2g}$.

Uses: [sk-cor-av-commutative], [sk-def-av-group-scheme], [sk-def-av-mult-n], [sk-def-av], [sk-prop-av-connected-order], [sk-prop-av-divisible-structure], [sk-prop-av-divisible], [sk-prop-av-finite-etale-points], [sk-prop-av-isogeny], [sk-prop-av-prime-p-etale]
