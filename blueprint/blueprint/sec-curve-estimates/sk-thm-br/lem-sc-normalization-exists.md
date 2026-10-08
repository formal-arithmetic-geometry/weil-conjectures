+++
id = "lem-sc-normalization-exists"
kind = "lemma"
title = "Existence and finiteness of the normalization"
order = 915
uses = ["def-sc-normalization"]
+++
Let $X$ be an integral scheme of finite type over a field $k$
and $\nu:X^{\nu}\to X$ its normalization in $k(X)$
([def-sc-normalization]). Then $\nu$ is finite, surjective
and birational; if $X$ is proper then $X^{\nu}$ is proper; and
$\dim X^{\nu}=\dim X$.

## Proof

By construction $\nu$ is affine and dominant, hence surjective
(its image is closed and contains the generic point of $X$).
Finiteness: for affine $X=\operatorname{Spec}A$ (the general
case follows by gluing), the normalization is
$\operatorname{Spec}\widetilde A$, where $\widetilde A$ is the
integral closure of $A$ in $k(X)$; we prove that
$\widetilde A$ is a finite $A$-module. If $\dim X=0$ this
is clear ($A$ is Artinian, hence finite over $k$). Assume
$\dim X=1$. By Noether normalization (*reference: Stacks
Project, Commutative Algebra,
[Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)*) there is a transcendental $x\in A$ such that
$A$ is finite over $k[x]$; then $\widetilde A$ equals the
integral closure of $k[x]$ in $k(X)$ (the integral closures of
$k[x]\subseteq A$ in their common fraction field $k(X)$
coincide), and $n:=[k(X):k(x)]<\infty$ (standard field theory:
*reference: Stacks Project, Fields: transcendence degree*).
Choose $b_1,\dots,b_n\in\widetilde A$ forming a $k(x)$-basis of
$k(X)$, and choose $0\neq s\in k[x]$ with
$s\,b_ib_j\in\sum_lk[x]b_l$ for all $i,j$ (clearing the
finitely many denominators of the multiplication table). We claim
$\widetilde A\subseteq(1/s)\sum_lk[x]b_l$. For
$b\in\widetilde A$, write $b=\sum_ic_ib_i$ with
$c_i\in k(x)$; for every $j$,

$$
s\,bb_j=\sum_ic_i(s\,b_ib_j)\in\sum_lk[x]b_l,
$$

so $s\,b\,M\subseteq M$ for $M:=\sum_lk[x]b_l$, and since
$1\in M\cap\widetilde A$ we get $s\,b=s\,b\cdot1\in M$, i.e. $b\in(1/s)M$. Thus $\widetilde A$ is a submodule of the
finitely generated free $k[x]$-module $(1/s)M$; since $k[x]$
is noetherian, $\widetilde A$ is finitely generated over
$k[x]$, hence over $A$. So $\nu$ is finite and birational.
A finite morphism is proper and preserves dimension, so if $X$
is proper then $X^{\nu}$ is proper, and
$\dim X^{\nu}=\dim X$.
