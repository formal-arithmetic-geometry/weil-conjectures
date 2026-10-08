+++
id = "lem-wf-point-count-linear-growth"
kind = "lemma"
title = "Linear growth of the point count on an affine curve"
order = 2652
uses = ["def-weil-pbc-scheme-conventions", "lem-zl-noether-normalization-dimension"]
+++
Let $U_0$ be a smooth affine curve over $k_0=\mathbf F_q$ (in the
separated finite-type
conventions of [def-weil-pbc-scheme-conventions]) and let
$k_n=\mathbf F_{q^n}$. Then there is a constant $d\ge1$ such that

$$
\#U_0(k_n)\le d\,q^n\qquad(n\ge1).
$$

## Proof

The affine curve is $\operatorname{Spec}(R)$ for the finite-type
$k_0$-algebra $R=\Gamma(U_0,\mathcal O_{U_0})$ of dimension one (in
the finite-type conventions of
[def-weil-pbc-scheme-conventions]). By
the Noether normalization theorem in dimension one
([lem-zl-noether-normalization-dimension]) there is a
finite injective $k_0$-algebra map $k_0[t]\hookrightarrow R$ with
$R$ a finite $k_0[t]$-module. This module is torsion-free: since
$U_0$ is smooth of pure dimension one, $R$ is a finite product of
one-dimensional (Dedekind) domains $R_1\times\cdots\times R_m$, and
each composite $k_0[t]\to R_i$ is injective, because if its kernel
were a nonzero prime $\mathfrak p$ then $R_i$ would be finite over the
field $k_0[t]/\mathfrak p$, hence zero-dimensional. A finitely
generated torsion-free module over the principal ideal domain
$k_0[t]$ is free; let $d$ be its rank (we may assume $U_0\neq\emptyset$,
so $d\ge1$), and let $f:U_0\to\mathbf A^1_{k_0}$ be the corresponding
finite morphism. Base change gives that $R\otimes_{k_0}k_n$ is a free
$k_n[t]$-module of rank $d$. A point $x\in U_0(k_n)$ with $f(x)=y$,
for $y\in k_n=\mathbf A^1_{k_0}(k_n)$, is a $k_n$-algebra map
$R\otimes_{k_0}k_n\to k_n$ sending $t$ to $y$, i.e. a $k_n$-algebra
map $A_y:=(R\otimes_{k_0}k_n)/(t-y)\to k_n$. Now $A_y$ is a
$k_n$-algebra of dimension $d$, and distinct $k_n$-algebra maps
$A_y\to k_n$ have distinct kernels, which are maximal ideals of $A_y$;
an artinian ring of $k_n$-dimension $d$ has at most $d$ maximal ideals
(by the Chinese remainder theorem). So each fiber of $f$ has at most
$d$ $k_n$-points, and $\mathbf A^1_{k_0}(k_n)$ has $q^n$ points, which
gives the estimate.

*Recorded in advance* from chapter *Boundary weights, constant twists, and real envelopes* of the source.
