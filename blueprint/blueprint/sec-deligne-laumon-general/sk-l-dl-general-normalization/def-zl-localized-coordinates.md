+++
id = "def-zl-localized-coordinates"
kind = "definition"
title = "Coordinates on a principal open of an affine base"
order = 2823
uses = ["def-sbc-affine-space", "def-weil-pbc-scheme-conventions"]
+++
Let $A$ be a domain, $B$ a finitely generated commutative
$A$-algebra, and $0\neq s\in A$. Write
$A_s=A[1/s]$, $B_s=B\otimes_A A_s$, and
$D(s)=\operatorname{Spec}A_s$.
For $d\geq0$ and a tuple $t=(t_1,\ldots,t_d)\in B_s^d$, define
the $D(s)$-morphism

$$
\nu_t:\operatorname{Spec}B_s\longrightarrow
\mathbf A^d_{D(s)}
$$

by the algebra homomorphism $A_s[T_1,\ldots,T_d]\to B_s$,
$T_i\mapsto t_i$. Here affine space has the meaning of
relative affine space; the map is
finite precisely when
$B_s$ is a finitely generated module over that polynomial ring.
No finiteness is included in the choice of $t$.
