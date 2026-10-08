+++
id = "lem-sc-frobenius-fixed-invariance"
kind = "lemma"
title = "Fixed points under algebraically closed base change"
lean = ["LinearMap.Frobenius.bijective_tmul_fixedPoints"]
order = 568
uses = ["lem-sc-lang-steinberg"]
+++
Let $k\subseteq k'$ be an extension of algebraically closed
fields of characteristic $p>0$, $V$ a finite-dimensional
$k$-vector space, and $F:V\to V$ a $p$-linear endomorphism
($F(\lambda v)=\lambda^pF(v)$, $F(v+w)=F(v)+F(w)$). Write
$V^F=\{v\in V:F(v)=v\}$ and let
$F':=F\otimes\sigma_{k'}:V\otimes_kk'\to V\otimes_kk'$ be the
base-changed $p$-linear map, where $\sigma_{k'}(x)=x^p$ is the
Frobenius of $k'$. Then the natural map

$$
V^F\longrightarrow(V\otimes_kk')^{F'},\qquad v\longmapsto v\otimes1,
$$

is an isomorphism of $\mathbf F_p$-vector spaces.

## Proof

Choose a $k$-basis $e_1,\dots,e_n$ of $V$ and write
$F(e_j)=\sum_ia_{ij}e_i$ with $a_{ij}\in k$. In the basis
$e_1\otimes1,\dots,e_n\otimes1$ of $V\otimes_kk'$, the map
$F'$ is

$$
F'(x_1,\dots,x_n)=\Bigl(\textstyle\sum_ja_{1j}x_j^p,\dots,
\sum_ja_{nj}x_j^p\Bigr),
$$

so the fixed points are the solutions in $(k')^n$ of the system
of polynomial equations

$$
x_i=\sum_{j=1}^na_{ij}x_j^p\qquad(1\leq i\leq n),
$$

whose coefficients lie in $k$. We claim the solution set in
$k'$ equals the solution set in $k$. By the proof of
[lem-sc-lang-steinberg] (Steps 1 and 2), the pair $(V,F)$
decomposes into cyclic blocks of the normal form

$$
F(x_1,\dots,x_m)=\bigl(a_1x_m^p,\,
x_1^p+a_2x_m^p,\,\dots,\,x_{m-1}^p+a_mx_m^p\bigr),
$$

and on such a block the equation $F(x)=x$ reads
$a_1x_m^p=x_1$ and
$x_{i-1}^p+a_ix_m^p=x_i$ for $2\leq i\leq m$; these equations give,
by the same recursion as in [lem-sc-lang-steinberg],

$$
x_i=\sum_{k=1}^{i}a_k^{p^{\,i-k}}x_m^{p^{\,i-k+1}}\qquad(1\leq i\leq m),
$$

and substituting into the last equation yields the polynomial
equation

$$
\varphi(x_m):=x_m-\sum_{k=1}^{m}a_k^{p^{\,m-k}}x_m^{p^{\,m-k+1}}=0.
$$

Since $\varphi$ has coefficients in $k$, is nonzero (its linear
coefficient is $1$), and $k$ is algebraically closed, all roots
of $\varphi$ lie in $k$. Hence the fixed points of $F'$ on
the block $k'\otimes_kk[e_1,\dots,e_m]$ are exactly the fixed
points of $F$ on the block: for every solution
$x_1,\dots,x_m$ of the above system, all coordinates are
polynomials in the last one $x_m$ with coefficients in $k$, and
$x_m$ is a root of $\varphi$, hence lies in $k$ – while
conversely every $x_m\in k$ with $\varphi(x_m)=0$ gives the
solution $x_i=\sum_{k=1}^{i}a_k^{p^{\,i-k}}x_m^{p^{\,i-k+1}}$
of the system. The natural map
$V^F\to(V\otimes_kk')^{F'}$ is injective
($v\otimes1=0$ implies $v=0$), and both sides decompose into the
same blockwise solution sets, so it is an isomorphism.
