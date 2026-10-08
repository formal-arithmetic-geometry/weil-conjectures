+++
id = "lem-sc-artin-schreier-dimension"
kind = "lemma"
title = "Artin–Schreier vanishing on a smooth curve"
order = 1008
uses = ["def-sc-constant-sheaves", "def-sc-curves", "def-weil-pbc-etale-cohomology", "lem-sc-affine-open-proper", "lem-sc-as-sequence", "lem-sc-compactification", "lem-sc-etale-affine-qcoherent", "lem-sc-ga-cohomology", "lem-sc-lang-steinberg"]
+++
Let $C$ be a smooth separated connected curve
over an algebraically closed field of characteristic $p>0$.
For the constant sheaf
$\mathbf F_p$, one has $H^q(C,\mathbf F_p)=0$ for $q>1$,
with cohomology as in [def-weil-pbc-etale-cohomology].

## Proof

By
[lem-sc-compactification] and [lem-sc-affine-open-proper]
the curve is either proper or affine. In the affine case,
[lem-sc-etale-affine-qcoherent] gives $H^q(C,\mathbf G_a)=0$
for $q>0$, so the Artin–Schreier long exact sequence gives
$H^q(C,\mathbf F_p)=0$ for $q>1$. We now treat the proper case.
The long exact sequence of the Artin–Schreier sequence
([lem-sc-as-sequence]),

$$
0\to H^0(C,\mathbf F_p)\to H^0(C,\mathbf G_a)\xrightarrow{\wp}
H^0(C,\mathbf G_a)\to H^1(C,\mathbf F_p)\to H^1(C,\mathbf G_a)
\xrightarrow{\wp}H^1(C,\mathbf G_a)\to H^2(C,\mathbf F_p)\to 0,
$$

(the terms $H^q(C,\mathbf G_a)$ vanish for $q\geq2$ by
[lem-sc-ga-cohomology]) identifies

$$
H^2(C,\mathbf F_p)=\operatorname{coker}\bigl(\wp:H^1(C,\mathcal O_C)\to H^1(C,\mathcal O_C)\bigr),
$$

where $\wp=F-1$ with $F$ the $p$-linear Frobenius
endomorphism of the finite-dimensional $k$-vector space
$H^1(C,\mathcal O_C)$; this cokernel is zero by
[lem-sc-lang-steinberg]. Hence
$H^q(C,\mathbf F_p)=0$ for $q>1$: for $q\geq3$ the
two adjacent $\mathbf G_a$ cohomology terms vanish, and the case
$q=2$ is the surjectivity just proved.
