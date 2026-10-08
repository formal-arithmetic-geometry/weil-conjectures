+++
id = "def-wf-lie-algebra"
kind = "definition"
title = "Lie algebras, ideals, solvability and Lie representations"
order = 2463
+++
Let $k$ be a field. A *Lie algebra* over $k$ is a $k$-vector space $L$
with a bilinear map $[\,\cdot,\cdot\,]:L\times L\to L$ (the *bracket*)
that is alternating, $[x,x]=0$, and satisfies the Jacobi identity

$$
[x,[y,z]]+[y,[z,x]]+[z,[x,y]]=0 .
$$

For example $\operatorname{End}(V)$, for a $k$-vector space $V$, is a
Lie algebra with $[X,Y]=XY-YX$, and so is every subspace closed under
this bracket. For $x\in L$ put $\operatorname{ad}(x)y=[x,y]$.

For subspaces $I,J\subseteq L$, write $[I,J]$ for the linear span of the
brackets $[x,y]$ with $x\in I$, $y\in J$. A *subalgebra* is a subspace
$I$ with $[I,I]\subseteq I$, and an *ideal* is a subspace $I$ with
$[L,I]\subseteq I$. If $I$ is an ideal, the quotient $L/I$ is a Lie
algebra with $[x+I,y+I]=[x,y]+I$. The *derived sequence* of a Lie
algebra $I$ is $D^0I=I$, $D^{n+1}I=[D^nI,D^nI]$ (also written
$I^{(n)}$), and $I$ is *solvable* if $D^nI=0$ for some $n$. $L$ is
*perfect* if $L=[L,L]$.

A *Lie representation* of $L$ on a $k$-vector space $V$ is a linear map
$r:L\to\operatorname{End}(V)$ with

$$
r([x,y])=r(x)r(y)-r(y)r(x)\qquad(x,y\in L).
$$

A subspace $U\subseteq V$ is *Lie-invariant* if $r(x)U\subseteq U$ for
all $x\in L$. The representation is *faithful* if $r$ is injective,
*simple* (irreducible) if $V\neq0$ and its only invariant subspaces are
$0$ and $V$, and *semisimple* if $V$ is a direct sum of simple invariant
subspaces. The map $\operatorname{ad}:L\to\operatorname{End}(L)$ is a
Lie representation (the *adjoint representation*), by the Jacobi
identity.
