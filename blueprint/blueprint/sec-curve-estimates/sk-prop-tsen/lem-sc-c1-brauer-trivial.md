+++
id = "lem-sc-c1-brauer-trivial"
kind = "lemma"
title = "The Brauer group of a $C_1$ field"
order = 895
uses = ["def-sc-cr-field"]
+++
Let $K$ be a $C_1$ field. Then
$\operatorname{Br}(K)=0$.

## Proof

We use the elementary structure theory of central simple algebras:
a finite central division algebra $D/K$ has dimension $d^2$,
and over a separable closure $K_s$ it becomes $M_d(K_s)$.
The algebraic inputs are the splitting and Wedderburn theorems
([Stacks Project, Tag 03R2](https://stacks.math.columbia.edu/tag/03R2))
and the fact that automorphisms of a matrix algebra are inner
([Stacks Project, Tag 074P](https://stacks.math.columbia.edu/tag/074P)).
Choose a $K$-basis $b_1,\ldots,b_{d^2}$ and a splitting
$\phi:D\otimes_KK_s\simeq M_d(K_s)$. Form the polynomial

$$
P(T_1,\ldots,T_{d^2})=
\det\left(\sum_i T_i\phi(b_i)\right).
$$

It is homogeneous of degree $d$. Changing the splitting conjugates
the matrix, leaving its determinant unchanged. For every
$\sigma\in\operatorname{Gal}(K_s/K)$, applying $\sigma$ to the
splitting gives another splitting, so every coefficient of $P$
is fixed by $\sigma$. Hence $P\in K[T_1,\ldots,T_{d^2}]$.
This defines the reduced norm; it is distinct from the determinant
of left multiplication on the $d^2$-dimensional space $D$.
For any nonzero $x\in D$, its inverse in $D$ remains an inverse
after applying $\phi$, so $P(x)\ne0$. If $d>1$, then
$d^2>d$, and [def-sc-cr-field] supplies a nonzero zero of
$P$, a contradiction. Therefore every central division algebra
has $d=1$ and equals $K$. Wedderburn's theorem now shows that
every central simple algebra is a matrix algebra over $K$, so
the Brauer group is zero.
