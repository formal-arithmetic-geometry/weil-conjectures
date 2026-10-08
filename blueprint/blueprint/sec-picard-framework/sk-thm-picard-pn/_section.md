+++
id = "sk-thm-picard-pn"
kind = "section"
title = "Cohomology of $\\PP^n$, Serre 1954"
order = 611
uses = ["sk-def-av-pic"]
lean = ["AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv", "AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne", "AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_top", "AlgebraicGeometry.ProjectiveSpace.nonempty_H_twist_top_equiv_dual"]
+++
*Theorem (sketch).*

Let $k$ be a field, $X=\PP^n_k$, $\cO(m):=\cO_X(m)$, and
$S^m(V)$ the $m$-th symmetric power of $V=k^{n+1}$.

$$
H^0(X,\cO(m))=S^m(V)\ (m\ge0),\qquad
H^q(X,\cO(m))=0\ (q\notin\{0,n\}),
$$

$$
H^n(X,\cO(m))=0\ (m\ge-n),\qquad
H^n(X,\cO(m))=S^{-m-n-1}(V)^{\vee}\ (m\le-n-1),
$$

the two top-degree clauses for $n\ge1$; for $n=0$, $X=\Spec k$ and
every $\cO(m)$ is $\cO_X$, so $H^0(X,\cO(m))=k$ for all $m$ and there is
no higher cohomology. In particular (for all $n\ge0$)
$\omega_X=\cO_X(-n-1)$ and $H^q(X,\cO_X)=k\cdot\delta_{q,0}$.

## Proof

On the standard affine cover
$\mathfrak U=\{D_+(x_0),\dots,D_+(x_n)\}$ the Čech complex is a
Koszul-type complex; by [sk-lem-picard-cech-computes] it computes
$H^*(X,\cO(m))$, the intersections $D_+(x_{i_0}\cdots x_{i_p})$ being
affine and $\PP^n_k$ separated over $k$. Koszul duality gives the
displayed answer.
