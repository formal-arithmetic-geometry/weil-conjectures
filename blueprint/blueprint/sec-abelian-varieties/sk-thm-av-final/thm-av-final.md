+++
id = "thm-av-final"
kind = "theorem"
title = "Abelian-variety estimate"
lean = ["AlgebraicGeometry.abelianVariety_estimate"]
order = 593
uses = ["def-sc-abelian-variety", "def-sc-isogeny", "def-sc-mult-n", "def-wf-abelian-tate-module", "lem-sc-connected-finite-order", "lem-sc-divisible-group-structure", "lem-sc-fg-order-prime-etale", "lem-sc-finite-flat-surj-points", "lem-sc-finite-nonempty-point", "lem-sc-isogeny-facts", "lem-sc-isogeny-surjective", "lem-sc-mult-n-finite-flat", "lem-sc-ntorsion-etale", "prop-av-tate-rank", "rem-ptr-sc-abelian-variety-1", "rem-ptr-sc-isogeny-2"]
+++
Let $A$ be an abelian variety of dimension $g$ over a field $k$, let
$p=\operatorname{char}k$ and let $n\ge1$.

- **(a)** $[n]:A\to A$ is a finite flat surjective homomorphism, hence
an isogeny of degree $n^{2g}$; $A[n]=\ker[n]$ is a finite flat group
scheme over $k$ of order $n^{2g}$.
- **(b)** If $p>0$, then $A[p^e]$ is finite flat of order $p^{2ge}$ for
every $e\ge1$. If $n$ is prime to $p$ (in particular if $p=0$), then
$A[n]$ is finite étale of rank $n^{2g}$.
- **(c)** Let $k$ be algebraically closed and $n$ prime to $p$. Then
$A[n](k)\cong(\Z/n\Z)^{2g}$, and for every extension
$k\subseteq k'$ of algebraically closed fields the canonical map
$A[n](k)\to A[n](k')$ is an isomorphism.
- **(d)** Let $k$ be algebraically closed. Then $A(k)$ is a divisible
abelian group, $A(k)[n]\cong(\Z/n\Z)^{2g}$ for every $n$ prime to $p$,
and for every prime $\ell\ne p$
$$
T_\ell A\cong\Z_\ell^{2g},\qquad V_\ell A\cong\Q_\ell^{2g}.
$$

## Proof

*(a)* This is exactly [lem-sc-isogeny-facts], [lem-sc-mult-n-finite-flat]: $[n]$ is a
homomorphism ([lem-sc-mult-n-homomorphism] with [lem-sc-av-commutative]), has
finite fibres ([lem-sc-mult-n-finite-kernel]) and is surjective
([lem-sc-mult-n-isogeny]), is flat with locally free pushforward of
rank the order of its kernel ([lem-sc-isogeny-degree]), and its
degree is computed as $n^{2g}$ from
$[n]^*\cN\cong\cN^{\otimes n^2}$ ([lem-sc-mult-n-pullback],
[lem-sc-ample-tensor]) together with
$\deg_{[n]^*\cN}(A)=\deg[n]\deg_{\cN}(A)$
([lem-sc-deg-pullback-finite]).

*(b)* The first clause is (a) with $n=p^e$. For the second,
$A[n]$ is finite flat of order $n^{2g}$ by (a); write
$G=A[n]$ and let $\bar k$ be an algebraic closure of $k$. Then
$G_{\bar k}=A_{\bar k}[n]$ is a finite flat group scheme over $\bar k$
of order $n^{2g}$, prime to $p$, so it is étale over $\bar k$ by
[lem-sc-fg-order-prime-etale] (for $p>0$: the identity component
$(G_{\bar k})^0$ is a connected finite flat group scheme, so its order
is a power of $p$ by [lem-sc-connected-finite-order] and divides
$n^{2g}$, whence $(G_{\bar k})^0=\Spec\bar k$; every connected
component of $G_{\bar k}$ is a translate of $(G_{\bar k})^0$ by a
$\bar k$-point, so $G_{\bar k}$ is reduced, hence étale over the
algebraically closed $\bar k$; for $p=0$ this is Cartier's theorem).
Finally étaleness descends to $k$: $G$ is flat over $k$ and
$\Omega_{G/k}\otimes_k\bar k\cong\Omega_{G_{\bar k}/\bar k}=0$, so
$\Omega_{G/k}=0$ and $G$ is étale over $k$. (The passage to
$\bar k$ is needed: over an imperfect $k$ a finite reduced $k$-scheme
need not be étale, so one cannot conclude directly from
$G^0=\Spec k$.)

*(c)* Assume $k$ algebraically closed and $n$ prime to $p$. By
(b), $A[n]$ is finite étale of order $n^{2g}$, so
$\lvert A[n](k)\rvert=n^{2g}$ and $A[n](k)\to A[n](k')$ is bijective
by [lem-sc-finite-etale-points]. The group structure
$(\Z/n\Z)^{2g}$ is the content of [lem-sc-ntorsion-etale]: the
prime-power case follows from divisibility of $A(k)$
([lem-sc-finite-flat-surj-points], [lem-sc-finite-nonempty-point], [lem-sc-isogeny-surjective]) and the structure theorem for torsion of a
divisible group ([lem-sc-divisible-group-structure]), and the general case
from the Chinese remainder theorem applied to the coprime-order
subgroup schemes $A[\ell_i^{e_i}]$.

*(d)* Still with $k$ algebraically closed:
$A(k)$ is abelian by [lem-sc-av-commutative] and divisible by
[lem-sc-finite-flat-surj-points], [lem-sc-finite-nonempty-point], [lem-sc-isogeny-surjective]; and $A(k)[n]\cong(\Z/n\Z)^{2g}$ for $n$ prime to
$p$ is clause (c). For the Tate module, each level
$A[\ell^n](k)\cong(\Z/\ell^n\Z)^{2g}$ by (c) and the transition maps
are surjective by [lem-sc-finite-flat-surj-points], [lem-sc-finite-nonempty-point], [lem-sc-isogeny-surjective], so the inverse limit
$T_\ell A$ of [def-wf-abelian-tate-module] is $\Z_\ell^{2g}$; this is
[prop-av-tate-rank], and $V_\ell A=T_\ell A\otimes\Q_\ell$.

Uses: [def-sc-isogeny], [rem-ptr-sc-isogeny-2], [def-sc-mult-n], [def-wf-abelian-tate-module], [def-sc-abelian-variety], [rem-ptr-sc-abelian-variety-1], [lem-sc-connected-finite-order], [lem-sc-divisible-group-structure], [lem-sc-finite-flat-surj-points], [lem-sc-finite-nonempty-point], [lem-sc-isogeny-surjective], [lem-sc-isogeny-facts], [lem-sc-mult-n-finite-flat], [lem-sc-ntorsion-etale], [lem-sc-fg-order-prime-etale], [prop-av-tate-rank]
