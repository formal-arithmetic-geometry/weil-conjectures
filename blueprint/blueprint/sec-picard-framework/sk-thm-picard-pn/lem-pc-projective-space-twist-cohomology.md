+++
id = "lem-pc-projective-space-twist-cohomology"
kind = "lemma"
title = "Monomial cohomology of twists on projective space"
order = 618
uses = ["def-pc-projective-space-twist", "lem-pc-affine-vanishing", "lem-pc-cech-computes", "lem-pc-twist-cocycle", "pqf-def-cohomology"]
lean = ["AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv", "AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne", "AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_top", "AlgebraicGeometry.ProjectiveSpace.nonempty_H_twist_top_equiv_dual"]
+++
Let $A$ be a commutative ring, $n\ge1$, and $d\in\mathbf Z$.
For the twisting modules
on $P=\mathbf P^n_A$, one has

$$
H^q(P,\mathcal O_P(d))\cong
\begin{cases}
\displaystyle\bigoplus_{\substack{e_i\ge0\\\sum e_i=d}} A\,x^e,&q=0,\\
\displaystyle\bigoplus_{\substack{e_i<0\\\sum e_i=d}} A\,x^e,&q=n,\\
0,&q\notin\{0,n\}.
\end{cases}
$$

Here $x^e=\prod_ix_i^{e_i}$, and the class of $x^e$ in degree $n$ is
that of the Cech $n$-cochain $x^e$ on $U_0\cap\cdots\cap U_n$.
In particular, for $n\ge1$, all these modules are finite free, and:

1. **(i)** $H^0(P,\mathcal O_P(d))$ is the degree-$d$ part
$A[x_0,\ldots,x_n]_d=S^d_A(V)$, the $d$-th symmetric power of the
free module $V=A^{n+1}$ with basis $x_0,\ldots,x_n$; it is zero
for $d<0$;
1. **(ii)** $H^n(P,\mathcal O_P(d))=0$ for $d\ge-n$, and
$H^n(P,\mathcal O_P(-n-1))$ is free of rank one with basis the class
of $x_0^{-1}x_1^{-1}\cdots x_n^{-1}$;
1. **(iii)** the groups in positive degree vanish for $d\ge0$;
in particular $H^0(P,\mathcal O_P)=A$ and
$H^q(P,\mathcal O_P)=0$ for $q\neq0$.

For $n=0$, every twist is free of rank one on
$\mathbf P^0_A=\operatorname{Spec}(A)$ and has no higher cohomology.

## Proof

The transition rule of [def-pc-projective-space-twist], whose gluing
is well defined by [lem-pc-twist-cocycle], identifies
sections on $U_J=\bigcap_{j\in J}U_j$ with the degree-$d$ part of
$A[x_0,\ldots,x_n,x_j^{-1}:j\in J]$.
Every $U_J$ is affine. By [lem-pc-cech-computes], the alternating
Cech complex on the $n+1$ standard opens computes cohomology.
Its terms are free $A$-modules on Laurent monomials $x^e$, where
$\sum_i e_i=d$ and $e_i\ge0$ for $i\notin J$. The differential
preserves $e$, so the complex is the direct sum, over those exponent
vectors, of complexes $C_e^\bullet$.

Put $N_e=\{i:e_i<0\}$. The degree-$p$ basis of $C_e^\bullet$
consists of the subsets $J\supseteq N_e$ of size $p+1$.
If $N_e=\varnothing$, this is the cochain complex of a simplex;
augmentation by $A$ in degree $-1$ makes it contractible, by
inserting any fixed vertex. Thus its only cohomology is $A$ in
degree zero. If $\varnothing\ne N_e\ne\{0,\ldots,n\}$, choose
$r\notin N_e$. Insertion of $r$ gives a contracting homotopy:
for a component indexed by $J$ not containing $r$, take the
component indexed by $J\cup\{r\}$ with sign
$(-1)^{\#\{j\in J:j<r\}}$, and set it to zero when $r\in J$.
The terms removing vertices other than $r$ cancel in $dh+hd$;
the term removing $r$ is the identity. The condition
$J\supseteq N_e$ is preserved. No degree-$-1$ term is needed,
because $N_e$ is nonempty. Finally, if $N_e=\{0,\ldots,n\}$,
the complex has just one copy of $A$, in degree $n$.

Direct sums of complexes of modules commute with cohomology, so
these three cases give the displayed formula. There are only
finitely many nonnegative exponent vectors of prescribed sum,
and only finitely many strictly negative ones.
For (i), the monomials $x^e$ with $e_i\ge0$ and $\sum e_i=d$ form
the standard basis of the degree-$d$ part of the polynomial ring,
which is $S^d_A(V)$ (the symmetric algebra of a free module is the
polynomial ring on a basis); there are none for $d<0$.
For (ii), strictly negative exponents satisfy $e_i\le-1$, so
$\sum e_i\le-n-1$; hence there are none for $d\ge-n$, and for
$d=-n-1$ the only one is $e=(-1,\ldots,-1)$. For (iii), when
$d\ge0$ there are no strictly negative exponent vectors at all, and
for $d=0$ the only nonnegative one is $e=0$, giving $H^0=A\cdot1$. For $n=0$ the single chart trivializes every
twist, and [lem-pc-affine-vanishing] proves its assertion.
The usual reference for this explicit calculation is
[Stacks, Section 30.8](https://stacks.math.columbia.edu/tag/01XS).
