+++
id = "def-weil-derived-complete"
kind = "definition"
title = "Derived complete objects"
order = 1457
uses = ["def-weil-completed-integral-coefficients", "def-weil-derived-limit", "def-weil-derived-tensor"]
+++
Use the completed integral coefficient sheaf
[def-weil-completed-integral-coefficients] $\widehat{\mathcal O}_{E,Y}$, its
reductions $(A_{E,n})_Y$, the derived category $D(Y_{\mathrm{proet}},\mathcal
O_E)$, and the restriction of scalars $\operatorname{Res}_n$ attached to
them, exact by [lem-weil-restriction-of-scalars-exact]. For a complex $K\in
D(Y_{\mathrm{proet}},\mathcal O_E)$ put

$$
 K_n:=K\otimes^L_{\mathcal O_E}A_{E,n},
$$

the derived tensor product [def-weil-derived-tensor] with the constant
$(A_{E,n})_Y$-module. The reduction morphisms $A_{E,n+1}\twoheadrightarrow
A_{E,n}$ make $(K_n)_{n\geq1}$ an inverse system in the single triangulated
category $D(Y_{\mathrm{proet}},\mathcal O_E)$, with transition maps
$\operatorname{Res}_{n+1}K_{n+1}\to\operatorname{Res}_nK_n$. Write

$$
 R\varprojlim_n\operatorname{Res}_nK_n
$$

for the derived limit [def-weil-derived-limit] of this inverse system, formed
inside the single triangulated category $D(Y_{\mathrm{proet}},\mathcal O_E)$
by its Roos triangle; no strict-tower model and no resolution of the system
is chosen, and the transition maps above are already maps in
$D(Y_{\mathrm{proet}},\mathcal O_E)$. The compatible maps $K\to
\operatorname{Res}_nK_n$ induce a canonical map

$$
 K\longrightarrow R\varprojlim_n\operatorname{Res}_nK_n,
$$

and $K$ is *derived complete* if this canonical map is an isomorphism. This
is the coefficient-sheaf form of Definition 15.93.4 of the Stacks Project,
Tag [091S](https://stacks.math.columbia.edu/tag/091S); the equivalent
description of derived completeness by a derived limit over the Koszul tower
$K_\bullet(A,f_1^n,\dots,f_r^n)$ of the generators of the ideal (in Situation
15.93.15 of the Stacks Project) is Lemma 15.93.17, Tag
[091Z](https://stacks.math.columbia.edu/tag/091Z).
