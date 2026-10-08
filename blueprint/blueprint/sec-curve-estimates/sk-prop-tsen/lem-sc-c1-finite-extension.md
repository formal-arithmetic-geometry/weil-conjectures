+++
id = "lem-sc-c1-finite-extension"
kind = "lemma"
title = "Finite extensions of $C_1$ fields"
order = 894
uses = ["def-sc-cr-field"]
+++
A finite extension $L/K$ of a
$C_1$ field $K$ is $C_1$.

## Proof

Write $m=[L:K]$, choose a $K$-basis $e_1,\ldots,e_m$ of $L$,
and let $F\in L[x_1,\ldots,x_N]$ be homogeneous of degree $d$,
where $N>d$. Introduce $mN$ variables $y_{ij}$, and set

$$
z_i=\sum_{j=1}^m e_jy_{ij},\qquad
Q(y)=\det_K\bigl(a\mapsto F(z_1,\ldots,z_N)a\bigr).
$$

Here the matrix is written in the chosen basis of $L$, with
coefficients in $K[y_{ij}]$; each entry is homogeneous of degree
$d$. Thus $Q$ is homogeneous of degree $md$, or is zero.
This determinant is the field norm of $F(z)$. For a tuple of
$K$-coordinates, $Q(y)=0$ if and only if $F(z)=0$: multiplication
by a nonzero element of the field $L$ is invertible. Since
$mN>md$, the $C_1$ property of [def-sc-cr-field] gives a
nonzero tuple $y$ with $Q(y)=0$; if $Q$ is the zero polynomial,
any nonzero tuple suffices. The basis property ensures that this
$y$ gives a nonzero tuple $(z_1,\ldots,z_N)\in L^N$.
Consequently $F$ has a nontrivial zero, proving that $L$ is $C_1$.
