+++
id = "sk-lem-coprojection"
kind = "section"
title = "Co-projection for a closed immersion"
order = 2005
uses = ["sk-def-purity-conv"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible"]
+++
*Lemma (sketch).*

Let $i:Z\hookrightarrow X$ be a closed immersion, let
$K\in D^b_{ctf}(X,\Lambda)$ and let $L$ be an *invertible* object of
$D^b_{ctf}(X,\Lambda)$. Then the canonical co-projection

$$
Ri^{!}\bigl(K\otimes^{\mathbb L}_{\Lambda_X}L\bigr)\ \xrightarrow{\ \sim\ }\
Ri^{!}K\otimes^{\mathbb L}_{\Lambda_Z}Li^{*}L
$$

is an isomorphism: an invertible tensor factor passes through $i^{!}$ at the
cost of restricting it. In particular, for $f:X\to Y$ with $f'=f\circ i$ and
$B$ invertible on $Y$, taking $L=Lf^{*}B$ and using
$Li^{*}Lf^{*}B\cong Lf'^{*}B$ gives

$$
Ri^{!}\bigl(K\otimes^{\mathbb L}_{\Lambda_X}Lf^{*}B\bigr)\ \cong\
Ri^{!}K\otimes^{\mathbb L}_{\Lambda_Z}Lf'^{*}B ;
$$

and for the Tate twists $L=\Lambda_X(m)[2m]$, whose restriction is
$\Lambda_Z(m)[2m]$, it reads
$Ri^{!}(K(m)[2m])\cong(Ri^{!}K)(m)[2m]$.
Iterating, for
$p_1,p_2:W=X\times_YX\to X$, $\Delta:W\supset X$ and $\omega_f$ invertible:

$$
R\Delta^{!}\bigl(Lp_1^{*}\omega_f\otimes^{\mathbb L}Lp_2^{*}\omega_f\bigr)
\ \cong\
\bigl(R\Delta^{!}\Lambda_W\bigr)\otimes^{\mathbb L}
L\Delta^{*}Lp_1^{*}\omega_f\otimes^{\mathbb L}L\Delta^{*}Lp_2^{*}\omega_f .
$$

## Proof

Test against an arbitrary $A\in D^b_{ctf}(Z,\Lambda)$ and use that $i$ is a
closed immersion, so $Ri_!=Ri_*$ and $Ri_*\dashv Ri^{!}$:

$$
\begin{aligned}
\operatorname{Hom}_Z\bigl(A,Ri^{!}(K\otimes L)\bigr)
&\cong\operatorname{Hom}_X\bigl(Ri_*A,\ K\otimes L\bigr)
&&\text{(adjunction)}\\
&\cong\operatorname{Hom}_X\bigl(Ri_*A\otimes L^{-1},\ K\bigr)
&&\text{($L$ invertible)}\\
&\cong\operatorname{Hom}_X\bigl(Ri_*(A\otimes Li^{*}L^{-1}),\ K\bigr)
&&\text{(projection formula for $Ri_*$)}\\
&\cong\operatorname{Hom}_Z\bigl(A\otimes Li^{*}L^{-1},\ Ri^{!}K\bigr)
&&\text{(adjunction)}\\
&\cong\operatorname{Hom}_Z\bigl(A,\ Ri^{!}K\otimes Li^{*}L\bigr)
&&\text{($Li^{*}L$ invertible).}
\end{aligned}
$$

The composite is natural in $A$ and is induced by the canonical co-projection
map, so Yoneda gives the asserted isomorphism. The displayed diagonal
identity is this applied twice on $W$, with $K=\Lambda_W$ and the invertible
factors $Lp_1^{*}\omega_f$, $Lp_2^{*}\omega_f$ — invertible because
$\omega_f$ is, by [sk-prop-cohsm] (a).

Uses: [sk-def-purity-conv]
