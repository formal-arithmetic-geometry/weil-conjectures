+++
id = "sk-d-real-weil"
kind = "section"
title = "Weil sheaves and their representations"
order = 2577
uses = ["sk-d-real-setup"]
lean = ["AlgebraicGeometry.WeilGroup", "AlgebraicGeometry.WeilGroup.IsLisse"]
+++
*Definition (sketch).*

Choose a geometric base point on the curve $C$.
Let $P=\pi_1(C)$ be its profinite etale fundamental group, defined by
the fiber functor on finite etale covers. The Weil group $W(C_0)$ is the
inverse image of the integer powers of geometric Frobenius in
$\pi_1(C_0)\to\Gal(k/\Fq)$. It has an exact degree sequence

$$
1\longrightarrow P\longrightarrow W(C_0)
\xrightarrow{\deg}\mathbf Z\longrightarrow0.
$$

A lisse Weil $\Qlb$-sheaf is equivalently a finite-dimensional
representation $\rho:W(C_0)\to\GL(V)$ admitting a finite coefficient
field $E/\Ql$ and an $E$-model whose restriction to $P$ is continuous
and preserves an $\mathcal O_E$-lattice. The quotient $\mathbf Z$ is
discrete. Choose a degree-one lift $\gamma$ and write $F=\rho(\gamma)$.
For a closed point $x$, the local Frobenius $F_x$ is the geometric
Frobenius at $x$: the image in $W(C_0)$ of the geometric Frobenius
element of a decomposition group $D_x\subset\pi_1(C_0)$ at $x$, i.e. of
the image of the geometric Frobenius of $\Gal(\overline{k(x)}/k(x))$
under $\pi_1(x)\to\pi_1(C_0)$ for a chosen path from a geometric point
over $x$ to the base point. It has degree $e_x$. Changing the path
conjugates it by some $g\in\pi_1(C_0)$, and this is already a
conjugation inside $W(C_0)$: identify $\Gal(k/\Fq)$ with
$\widehat{\mathbf Z}$ by sending geometric Frobenius to $1$, so that
$\deg$ extends to $\pi_1(C_0)\to\widehat{\mathbf Z}$ with
$W(C_0)=\deg^{-1}(\mathbf Z)$. Since
$\widehat{\mathbf Z}=\mathbf Z+e_x\widehat{\mathbf Z}$, write
$\deg g=n+e_xt$ with $n\in\mathbf Z$ and $t\in\widehat{\mathbf Z}$, and
let $F_x^t$ be the image of the $t$-th power of geometric Frobenius in
the procyclic group $\Gal(\overline{k(x)}/k(x))\simeq\widehat{\mathbf Z}$;
it has degree $e_xt$ and commutes with $F_x$. Then $w=gF_x^{-t}$ has
degree $n$, so $w\in W(C_0)$, and
$gF_xg^{-1}=wF_x^{t}F_xF_x^{-t}w^{-1}=wF_xw^{-1}$. Hence conjugacy in
$\pi_1(C_0)$ and in $W(C_0)$ agree on $F_x$, and $F_x$ is well defined
up to conjugacy in $W(C_0)$.
A constructible Weil sheaf is lisse of finite rank on each stratum of a
finite stratification into locally closed subschemes.

Uses: [sk-d-real-setup]
