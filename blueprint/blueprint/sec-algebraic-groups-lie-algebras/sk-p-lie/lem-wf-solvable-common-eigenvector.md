+++
id = "lem-wf-solvable-common-eigenvector"
kind = "lemma"
title = "Common eigenvector for a solvable Lie algebra"
order = 2473
+++
Let a finite-dimensional solvable Lie algebra $\mathfrak r$ over
$\Qlb$ act on a nonzero finite-dimensional vector space $M$.
Then there are $0\ne v\in M$ and a linear form
$\lambda:\mathfrak r\to\Qlb$ such that

$$
Xv=\lambda(X)v\quad(X\in\mathfrak r),
\qquad \lambda([\mathfrak r,\mathfrak r])=0.
$$

## Proof

Induct on $\dim\mathfrak r$. If $\mathfrak r=0$, take any
nonzero $v\in M$ and the zero functional $\lambda=0$. Otherwise
choose a codimension-one ideal
$\mathfrak a\supseteq[\mathfrak r,\mathfrak r]$ and write
$\mathfrak r=\mathfrak a\oplus\Qlb X$. By induction there are
$0\ne v\in M$ and $\lambda\in\mathfrak a^*$ with
$Av=\lambda(A)v$ for every $A\in\mathfrak a$. Let
$U=\operatorname{span}\{X^jv:j\ge0\}$. From

$$
AX^j=X^jA+\sum_{i=0}^{j-1}X^i[A,X]X^{j-1-i}
$$

and $[A,X]\in\mathfrak a$, induction on $j$ shows that $U$ is
$\mathfrak a$-stable and that, in the ordered spanning sequence
$v,Xv,X^2v,\ldots$, every $A\in\mathfrak a$ is upper triangular
with constant diagonal entry $\lambda(A)$. The space $U$ is also
$X$-stable. Therefore

$$
0=\operatorname{tr}_U([X,A])=(\dim U)\lambda([X,A]),
$$

and characteristic zero gives $\lambda([X,A])=0$.

The simultaneous $\lambda$-eigenspace
$U_\lambda=\{u\in U:Au=\lambda(A)u\ (A\in\mathfrak a)\}$ contains
$v$, and the last equality shows that it is $X$-stable. Since the
ground field is algebraically closed, $X|_{U_\lambda}$ has an
eigenvector. Extending $\lambda$ by its corresponding eigenvalue on
$X$ gives the required common eigenvector; its vanishing on the
derived algebra follows from

$$
[\mathfrak r,\mathfrak r]
=[\mathfrak a,\mathfrak a]+[X,\mathfrak a]:
$$

the induction hypothesis kills the first summand and the trace
calculation above kills the second.
