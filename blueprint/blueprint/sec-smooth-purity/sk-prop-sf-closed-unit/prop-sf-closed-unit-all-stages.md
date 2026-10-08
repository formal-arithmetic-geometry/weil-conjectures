+++
id = "prop-sf-closed-unit-all-stages"
kind = "theorem"
title = "Closed direct image is fully faithful at every coefficient stage"
order = 1861
tags = ["latex:proposition"]
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-exceptional-inverse-image", "def-weil-rationalization-karoubi", "prop-sf-closed-immersion-unit", "prop-weil-open-closed-recollement-adjunctions", "prop-weil-pbc-direct-image-limits", "prop-weil-pbc-roos-triangle", "prop-weil-pbc-scalar-extension"]
+++
Let $i:Z\hookrightarrow X$ be a closed immersion of separated finite-type
$k$-schemes and let $\Lambda$ be one of the coefficient stages
$A_{E,n},\mathcal O_E,E,\Qlb$, with the categories $D^b_c(-,\Lambda)$ of
[def-weil-derived-complete-integral-detailed],
[def-weil-rationalization-karoubi],
[def-weil-algebraically-closed-coefficients] and the direct image
$i_*=Ri_*=Ri_!$ of [def-weil-derived-direct-image]. Then

$$
i_*:D^b_c(Z,\Lambda)\longrightarrow D^b_c(X,\Lambda)
$$

is fully faithful. Consequently, at every stage at which $i_*$ has a right
adjoint $Ri^!$ on these categories (the exceptional inverse image of
[def-weil-exceptional-inverse-image]), the adjunction unit is an isomorphism

$$
Q\xrightarrow{\ \sim\ }Ri^!i_*Q\qquad(Q\in D^b_c(Z,\Lambda)).
$$

At $\Lambda=A_{E,n}$ the right adjoint exists on the ambient categories and
this is [prop-sf-closed-immersion-unit].

## Proof

*Finite stage.* By [prop-weil-open-closed-recollement-adjunctions] the
counit $i^*i_*\to\operatorname{id}$ of $i^*\dashv i_*$ is an isomorphism, so
$i_*$ is fully faithful on the ambient categories and hence on the full
subcategories $D^b_c$.

*Integral stage.* Put $R=\mathcal O_E$ and $A_n=R/\varpi_E^n$. For
$P,Q\in D^b_c(Z,R)$ one has $Q\cong R\varprojlim_n\operatorname{Res}_nQ_n$
and, by [prop-weil-pbc-direct-image-limits],
$i_*Q\cong R\varprojlim_n\operatorname{Res}_ni_*Q_n$ with
$(i_*P)_n\cong i_*P_n$. Extension and restriction of scalars give
$\operatorname{Hom}(P[m],\operatorname{Res}_nQ_n)
=\operatorname{Hom}_{A_n}(P_n[m],Q_n)$ and
$\operatorname{Hom}(i_*P[m],\operatorname{Res}_ni_*Q_n)
=\operatorname{Hom}_{A_n}(i_*P_n[m],i_*Q_n)$, and $i_*$ identifies the two by
the finite stage, compatibly with the transition maps. Apply
$\operatorname{Hom}(P[m],-)$ and $\operatorname{Hom}(i_*P[m],-)$ to the two
Roos triangles of [prop-weil-pbc-roos-triangle]; the map induced by $i_*$ is
an isomorphism on the two product terms for all $m$, so by the five lemma
$\operatorname{Hom}(P,Q)\to\operatorname{Hom}(i_*P,i_*Q)$ is bijective.

*Rational stage.* Hom groups in $D^b_c(-,E)$ are the integral ones tensored
with $E$ ([def-weil-rationalization-karoubi]), and $i_*$ is the
rationalized integral functor, so bijectivity persists.

*Algebraically closed stage.* Hom groups in $D^b_c(-,\Qlb)$ are filtered
colimits over finite extensions $L$ of Hom groups at the stage $L$
([def-weil-algebraically-closed-coefficients]), and $i_*$ commutes with
finite scalar extension ([prop-weil-pbc-scalar-extension]); a colimit of
bijections is a bijection.

*The unit.* Given a right adjoint $Ri^!$ at the stage $\Lambda$, fix $Q$.
For every $P$ the composite of $\eta_Q\circ-:\operatorname{Hom}(P,Q)\to
\operatorname{Hom}(P,Ri^!i_*Q)$ with the adjunction bijection onto
$\operatorname{Hom}(i_*P,i_*Q)$ is, by a triangle identity, $g\mapsto i_*g$,
which is bijective by full faithfulness. So $\eta_Q\circ-$ is bijective,
naturally in $P$, and Yoneda makes $\eta_Q$ an isomorphism, exactly as in
[prop-sf-closed-immersion-unit].
