+++
id = "lem-pc-projective-space-serre-pairing"
kind = "lemma"
title = "Top cohomology of twists on projective space as a dual"
order = 619
uses = ["def-pc-projective-space-twist", "lem-pc-cech-computes", "lem-pc-projective-space-twist-cohomology", "lem-pc-twist-tensor", "pqf-def-cohomology"]
+++
Let $A$ be a commutative ring, $n\ge1$, $P=\mathbf P^n_A$ with the
standard opens $U_i=D_+(x_i)$ and twists $\mathcal O_P(d)$ of
[def-pc-projective-space-twist], and let $V=A^{n+1}$ be the free
module with basis $x_0,\ldots,x_n$. For $a,b\in\mathbf Z$, multiplying
a Cech cochain $(c_J)_J$ of $\mathcal O_P(b)$ on the standard cover by
a global section $s$ of $\mathcal O_P(a)$, componentwise
$c_J\mapsto s|_{U_J}c_J$ through the isomorphism
$\mathcal O_P(a)\otimes\mathcal O_P(b)\cong\mathcal O_P(a+b)$ of
[lem-pc-twist-tensor], induces an $A$-bilinear pairing

$$
H^0(P,\mathcal O_P(a))\times H^n(P,\mathcal O_P(b))\longrightarrow
H^n(P,\mathcal O_P(a+b)).
$$

For $d\ge0$ the pairing

$$
H^0(P,\mathcal O_P(d))\times H^n(P,\mathcal O_P(-d-n-1))\longrightarrow
H^n(P,\mathcal O_P(-n-1))=A\cdot\bigl[x_0^{-1}\cdots x_n^{-1}\bigr]\cong A
$$

is perfect: in the monomial bases of
[lem-pc-projective-space-twist-cohomology], $x^f$ pairs to $1$ with
$x^{-f-\mathbf 1}$, where $\mathbf 1=(1,\ldots,1)$, and to $0$ with every
other basis element. Consequently, for every $m\le-n-1$,

$$
H^n(P,\mathcal O_P(m))\cong
\operatorname{Hom}_A\bigl(S^{-m-n-1}_A(V),A\bigr)=S^{-m-n-1}(V)^{\vee}
$$

canonically, while $H^n(P,\mathcal O_P(m))=0$ for $m\ge-n$. For $A=k$ a
field this is the description
$H^n(\mathbf P^n_k,\mathcal O(m))=S^{-m-n-1}(k^{n+1})^{\vee}$.

## Proof

Restriction of sections is multiplicative and the isomorphism of
[lem-pc-twist-tensor] is compatible with restriction, so
multiplication by $s$ commutes with the alternating Cech differential.
It therefore induces a map on Cech cohomology of the standard cover,
which is $H^*(P,-)$ of the twists by [lem-pc-cech-computes] (all
intersections $U_J$ are affine); the resulting map is $A$-bilinear in
$(s,c)$.

As in the proof of [lem-pc-projective-space-twist-cohomology],
sections of $\mathcal O_P(d)$ over $U_J$ are identified with the
degree-$d$ part of $A[x_0,\ldots,x_n,x_j^{-1}:j\in J]$, the monomial
$x^e$ corresponding on $U_i$ to $(x^e/x_i^{d})\,e_i^{(d)}$. Since
[lem-pc-twist-tensor] sends $e_i^{(a)}\otimes e_i^{(b)}$ to
$e_i^{(a+b)}$, the product of sections corresponds to the product of
Laurent polynomials. Hence the pairing of $x^f$ ($f_i\ge0$,
$\sum f_i=d$) with the class of the Cech $n$-cochain $x^e$ on
$U_0\cap\cdots\cap U_n$ ($e_i<0$, $\sum e_i=-d-n-1$) is the class of
the $n$-cochain $x^{e+f}$.

That proof decomposes the Cech complex of $\mathcal O_P(-n-1)$ as a
direct sum of complexes $C_g^\bullet$ over exponent vectors $g$ with
$\sum g_i=-n-1$, and shows that the degree-$n$ cohomology of
$C_g^\bullet$ is zero unless all $g_i<0$ (for $N_g=\varnothing$ the
cohomology sits in degree $0<n$, and for
$\varnothing\ne N_g\ne\{0,\ldots,n\}$ the complex is contractible).
So the class of $x^{e+f}$ vanishes unless $e_i+f_i\le-1$ for all $i$;
as $\sum_i(e_i+f_i)=-n-1$, this happens exactly when
$e_i+f_i=-1$ for all $i$, i.e. $e=-f-\mathbf 1$, and then the class is
the basis element $[x_0^{-1}\cdots x_n^{-1}]$. The map
$f\mapsto-f-\mathbf 1$ is a bijection from the nonnegative exponent
vectors of sum $d$ to the strictly negative ones of sum $-d-n-1$
(inverse $e\mapsto-e-\mathbf 1$). Thus, in the monomial bases, the
pairing has the matrix of this bijection, so it is perfect, and the
induced map
$H^n(P,\mathcal O_P(-d-n-1))\to\operatorname{Hom}_A(H^0(P,\mathcal O_P(d)),A)$
sends a basis to the dual basis and is an isomorphism of finite free
modules. With $d=-m-n-1\ge0$ and
$H^0(P,\mathcal O_P(d))=S^d_A(V)$
([lem-pc-projective-space-twist-cohomology] (i)) this is the
displayed isomorphism; it is canonical, being defined by the pairing
and the basis $[x_0^{-1}\cdots x_n^{-1}]$ of
$H^n(P,\mathcal O_P(-n-1))$. The vanishing for $m\ge-n$ is
[lem-pc-projective-space-twist-cohomology] (ii).
