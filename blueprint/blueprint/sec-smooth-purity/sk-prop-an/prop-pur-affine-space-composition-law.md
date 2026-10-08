+++
id = "prop-pur-affine-space-composition-law"
kind = "theorem"
title = "Affine-space composition law"
order = 1977
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-pur-affine-space-comparison", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, and let $d,e\geq1$. Under the canonical identification
$\mathbf A^{d+e}_Y\cong\mathbf A^d_{\mathbf A^e_Y}$, the equality

$$
\gamma_{p_{d+e},K}
=
c_{p_e,p_d}^{-1}\circ
\gamma_{p_d,Rp_e^!K}\circ
Lp_d^*(\gamma_{p_e,K})(d)[2d]
$$

holds after the canonical reassociation of twists and shifts, where
$c_{g,f}:R(gf)^!\cong Rf^!Rg^!$ is the composition isomorphism for the
exceptional inverse image. The Koszul sign interchanging the two
$A(1)$-tensor factors in the product of $(d)[2d]$ and $(e)[2e]$ is
$+1$, both factors being of even degree; the two orderings of the affine
coordinates give the same composite comparison.

## Proof

Step 1: unpack the definition. By [def-pur-affine-space-comparison],
$\gamma_{p_{d+e},K}$ is defined as the ordered composite of the
$d+e$ affine-line comparisons
$\gamma_{p_1,-}$ applied to the tower

$$
\mathbf A^{d+e}_Y\to\mathbf A^{d+e-1}_Y\to\cdots\to Y,
$$

with the composition isomorphisms for the exceptional inverse image of a
composite morphism and the additivity isomorphisms for the twists, and
the natural identification $Lp_{d+e}^*K\cong Lp_d^*Lp_e^*K$ of the
pullback-composition. Step 2: the reassociation. The right-hand side
of the displayed equality is the same ordered composite
$(\gamma_{p_e,K},\ \gamma_{p_d,Rp_e^!K})$ except that the regroupation
of the $d+e$ factors into the last $e$ coordinates and the first
$d$ coordinates is made explicit: both sides are the composite of
the $d+e$ affine-line comparisons ordered by the coordinate
$(x_1,\ldots,x_{d+e})$, and the two regroupings differ only by the
associativity of the composition isomorphism $c_{g,f}$ of
[def-weil-exceptional-inverse-image] – the reassociation
pentagon for the triple $(R^!$-isomorphisms of the three stages of
the tower), the unit laws, and the compatibility of the
twist-additivity isomorphisms. Step 3: the signs. The shift of
$K(d)[2d]$ produced by $d$ factors is $2d$, and the symmetry of
the tensor product interchanging the two blocks of "degrees" $2a$ and
$2b$ (the total shifts of the two blocks, $a$ and $b$ factors
each) carries the Koszul sign $(-1)^{(2a)(2b)}=+1$; the
twist-additivity isomorphisms similarly involve only even-degree
factors, so the reorderings of the coordinates produce no sign at all.
Step 4: the conclusion. By Steps 2 and 3 the composite comparison is
invariant under the permutation $(1,\ldots,d+d')\to(d+1,\ldots,d+e,1,\ldots,d)$ of the block order, which is exactly the displayed
equality, both orderings giving the same global morphism.
