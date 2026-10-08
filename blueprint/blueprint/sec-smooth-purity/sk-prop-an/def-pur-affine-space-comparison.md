+++
id = "def-pur-affine-space-comparison"
kind = "definition"
title = "Affine-space comparison"
order = 1976
uses = ["def-coefficient-twists-detailed", "def-pur-affine-line-purity-comparison", "def-pur-conventions", "def-sbc-affine-space", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, and write $p_d:\mathbf A^d_Y\to Y$ for the projection of
[def-sbc-affine-space], $d\geq0$, obtained as the iterated composite
of $d$ affine-line projections. For every $K\in D^b_{ctf}(Y,\Lambda)$
define

$$
\gamma_{p_d,K}:Lp_d^*K(d)[2d]\longrightarrow Rp_d^!K
$$

as the ordered composite of the $d$ affine-line purity comparisons
[def-pur-affine-line-purity-comparison], the composition isomorphisms
for the (coherently associative) exceptional inverse image of a composite
morphism, and the additivity isomorphisms for the
Tate twists. For $d=0$,
$\gamma_{p_0,K}$ is the identity of $K$.
