+++
id = "lem-pc-twist-cocycle"
kind = "lemma"
title = "The cocycle rule for the transition units of the twists"
order = 615
uses = ["def-pc-proj", "def-pc-projective-space-twist"]
+++
Let $A$ be a commutative ring, $n\ge0$ and
$P=\operatorname{Proj}(A[x_0,\ldots,x_n])$ with standard affine opens
$U_i=D_+(x_i)$, and let $d\in\mathbf Z$
([def-pc-projective-space-twist]). Then the units
$u_{ij}:=(x_i/x_j)^d\in\Gamma(U_i\cap U_j,\mathcal O_P^*)$ satisfy
$u_{ij}u_{jk}=u_{ik}$ on $U_i\cap U_j\cap U_k$, for all
$i,j,k\in\{0,\ldots,n\}$.

## Proof

By [def-pc-proj] the rings
$\Gamma(U_i\cap U_j\cap U_k,\mathcal O_P)$ are localizations of the
polynomial ring $A[x_0,\ldots,x_n]$, and by
[def-pc-projective-space-twist] the units $u_{ij}$ are the $d$-th
powers of the units $x_i/x_j$ there. On $U_i\cap U_j\cap U_k$ one has
$(x_i/x_j)(x_j/x_k)=x_i/x_k$, hence

$$
u_{ij}u_{jk}=(x_i/x_j)^d(x_j/x_k)^d=(x_i/x_k)^d=u_{ik},
$$

the middle equality being the multiplicativity of the power map on
units (for $d<0$ it is applied to the inverse units).
