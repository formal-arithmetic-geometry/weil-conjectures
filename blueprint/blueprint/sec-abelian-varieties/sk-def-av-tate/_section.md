+++
id = "sk-def-av-tate"
kind = "section"
title = "$\\ell$-adic Tate module"
lean = ["AlgebraicGeometry.IsAbelianScheme.tateModule"]
order = 469
+++
*Definition (sketch).*

Let $A$ be an abelian variety over $k$ and $\ell\ne\operatorname{char}k$
a prime. The *$\ell$-adic Tate module* of $A$ is the inverse
limit

$$
T_\ell A:=\varprojlim_n A[\ell^n](\bar k),
$$

the transition map from level $n+1$ to level $n$ being multiplication
by $\ell$; its rational form is $V_\ell A:=T_\ell A\otimes_{\Z_\ell}\Q_\ell$.
Every endomorphism of $A$, and every semilinear automorphism of
$A_{\bar k}$ over an automorphism of $k$, acts componentwise on
$T_\ell A$, so that $T_\ell A$ is a $\Z_\ell$-module with an action of
$\operatorname{Gal}(\bar k/k)$ in the arithmetic case.
