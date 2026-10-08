+++
id = "lem-galois-glue"
kind = "lemma"
title = "Glueing of schemes along open immersions"
order = 963
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $Y$ be a scheme, let $\{Y_i\to Y\}$ be a Zariski cover, and for
each $i$ let $P_i\to Y_i$ be a scheme. Suppose given isomorphisms
$\varphi_{ij}:P_i\times_YY_j\to P_j\times_YY_i$ over $Y_i\times_YY_j$
with $\varphi_{ii}=\operatorname{id}$ and
$\varphi_{jk}\varphi_{ij}=\varphi_{ik}$ over the triple intersections.
Then there is a $Y$-scheme $P$ with isomorphisms
$P\times_YY_i\cong P_i$ over $Y_i$ compatible with the
$\varphi_{ij}$, unique up to unique isomorphism.

## Proof

Form $P_0=\coprod_iP_i$ and
$R=\coprod_{i,j}P_i\times_YY_j$, with the two maps $s,t:R\to P_0$
given on the $(i,j)$-component by $\operatorname{id}\times Y_j$ and
$\varphi_{ij}$ (the coproducts and fibre products of schemes being
those of [def-weil-pbc-scheme-conventions]). Both are open immersions, and the cocycle condition
says that they define an equivalence relation on the underlying
topological space. The quotient topological space $P$ therefore
carries the sheaf of rings
$U\mapsto\{(f_i):\varphi_{ij}^*f_j=f_i\text{ on overlaps}\}$, a sheaf by
the cocycle condition, and the maps $P_i\to Y_i\to Y$ glue to
$P\to Y$; the restrictions $P\times_YY_i\cong P_i$ are the quotient
maps. Uniqueness is the uniqueness of the quotient.
