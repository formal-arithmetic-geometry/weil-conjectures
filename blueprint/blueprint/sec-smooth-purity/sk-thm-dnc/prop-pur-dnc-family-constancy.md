+++
id = "prop-pur-dnc-family-constancy"
kind = "theorem"
title = "The deformation family is constant along the affine line"
order = 2001
tags = ["latex:proposition"]
uses = ["cor-pur-vector-bundle-purity", "def-pur-co-smoothness", "def-pur-conventions", "def-pur-dnc-section-family", "def-weil-derived-tensor", "lem-pur-concentrated-complex-shift", "lem-pur-dnc-section-geometry", "prop-pur-a1-invariance", "thm-pur-cohomological-smoothness"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), in the situation of
[def-pur-dnc-section-family] with family object $F$, let
$a:\mathbf A^1_B\to B$ be the projection and let
$i_1:B\to\mathbf A^1_B$ be the section $t=1$.

1. *the family is a shift of a lisse line.* The family object
is a shift of a finite locally constant rank-one sheaf,
$$
F\simeq\mathcal L_F(d)[2d],
$$
and likewise $C(g,s)\simeq\mathcal L_1(d)[2d]$ on $B$; in
particular no descent of an object or of a morphism of a derived
category is needed below.
1. *constancy along the affine line.* There is a canonical
isomorphism
$$
\kappa:\;F\;\xrightarrow{\ \sim\ }\;a^*C(g,s).
$$
Since $i_1^*a^*C(g,s)=C(g,s)=i_1^*F$ by
[lem-pur-dnc-section-geometry](1), the family object is the
pullback of its own fibre at $t=1$: the deformation family is
constant along $\mathbf A^1_B$ over $B$.
1. *normalization and uniqueness.* $\kappa$ is the unique
isomorphism $F\to a^*C(g,s)$ which at the section $t=1$
restricts to the identity of $C(g,s)$ under the identification
$i_1^*F\simeq C(g,s)$ of
[lem-pur-dnc-section-geometry](1).
1. *locality and base change.* $\kappa$ is compatible with
etale localization on $B$ and with arbitrary base change
$B'\to B$.

## Proof

The family object is the one of [def-pur-dnc-section-family]; tensor inverses and shifts are understood as in [def-weil-derived-tensor].
Write $a:\mathbf A^1_B\to B$ and let $i_1:B\to\mathbf A^1_B$ be the
unit section.

Step 1: the family object is a shift of a lisse rank-one line. By
[lem-pur-dnc-section-geometry](2),
$\widetilde g$ is smooth, so $\omega_{\widetilde g}$ is invertible
by [thm-pur-cohomological-smoothness]; by (2) and (4) it is etale-locally
$\Lambda(d)[2d]$, hence so is $F$. An etale cover of $B$ on
which the pair $(V,s)$ has standard coordinates also carries the
family to the standard model, so
[lem-pur-concentrated-complex-shift] applied to that cover gives

$$
F\;\simeq\;\mathcal L_F(d)[2d],
$$

with $\mathcal L_F$ a finite locally constant rank-one sheaf on
$\mathbf A^1_B$; the same argument gives
$C(g,s)\simeq\mathcal L_1(d)[2d]$ on $B$. This is (1), and this
reduction to actual sheaves is the point which makes the glueing at the
end of the proof the ordinary sheaf axiom.
Step 2: the local models and their normalization. Refine the etale
cover so that in addition $C(g,s)|_{B_i}$ is a shift-twist of the free
rank-one module; such a refinement exists because $C(g,s)$ is finite
locally constant by Step 1. Let $B_i\to B$ be the resulting cover,
on which there are coordinates of pairs
$(V_i,s_i)\to(\mathbf A^d_{B_i},0)$
([lem-pur-dnc-section-geometry](2)); for the standard pair the
deformation space is
$\mathbf A^d_{B_i}\times_{B_i}\mathbf A^1_{B_i}$, $x_k=tu_k$.
Exceptional pullback along the coordinate map is ordinary pullback, and
the vector-bundle Thom calculation
([cor-pur-vector-bundle-purity] as in
[lem-pur-dnc-section-geometry](4)) supplies an isomorphism

$$
\kappa_i:F|_{\mathbf A^1_{B_i}}\xrightarrow{\ \sim\ }
a_i^*C(g,s)|_{B_i},
$$

whose restriction $\kappa_i(1)$ is an automorphism of the free
rank-one sheaf on $B_i$. Multiplying $\kappa_i$ by the pullback
of its inverse $a_i^*(\kappa_i(1)^{-1})$ normalizes it to the
identity at $t=1$, on every connected component of $B_i$.
Step 3: gluing and uniqueness, i.e. (2) and (3). Apply
[prop-pur-a1-invariance] over the base $Y=B$ with $C=C(g,s)$, with
$\theta:i_1^*F\xrightarrow{\sim}C(g,s)$ the identification of
[lem-pur-dnc-section-geometry](1), and with the cover $\{B_i\to B\}$ of
Step 2, whose members may be taken affine, hence separated of finite type
over $k$. Its hypotheses hold: the *local shape* because
$F\simeq\mathcal L_F(d)[2d]$ by Step 1, and the *normalized local
comparisons* are the $\kappa_i$ of Step 2, which restrict at $t=1$ to the
identity of $C(g,s)|_{B_i}$ under $\theta$. Its gluing assertion gives a
unique isomorphism

$$
\kappa:F\xrightarrow{\ \sim\ }a^*C(g,s)
$$

restricting to every $\kappa_i$, hence to the identity at $t=1$: this is
(2), and existence in (3). Its uniqueness assertion says that $\kappa$ is
the only isomorphism $F\to a^*C(g,s)$ restricting to $\theta$, i.e. to the
identity of $C(g,s)$, at $t=1$, which is the uniqueness in (3).
Finally, the Rees-algebra description of the DNC
for the closed section, the local standard models, and the localized
Thom classes all commute with base change and etale localization, hence
so does the resulting isomorphism: this is (4).
