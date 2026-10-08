+++
id = "sk-prop-sf-closed-unit"
kind = "section"
title = "Closed-immersion unit"
order = 1852
uses = ["sk-def-sf-operations", "sk-prop-sf-existence"]
lean = ["AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app"]
+++
*Proposition (sketch).*

For a closed immersion $i:Z\hookrightarrow X$ of finite-type $k$-schemes and
$Q\in\Dctf(Z,\Lambda)$, the exceptional adjunction unit of
[sk-def-sf-operations] is an isomorphism

$$
Q\xrightarrow{\ \eta_i^!\ }Ri^!Ri_*Q,
$$

where $Ri_!=Ri_*$ because $i$ is proper.

## Proof

The direct image of a closed immersion is exact and satisfies
$i^*i_*\cong\operatorname{id}$ — on geometric stalks over $Z$ the two sides
agree and $i_*$ vanishes off $Z$ — so $Ri_*$ is fully faithful. Since $i$
is proper, $Ri_!=Ri_*$, and $Ri^!$ is its right adjoint
([sk-prop-sf-existence], unconditional on the ordinary étale derived
categories). Hence for every $P\in\Dctf(Z,\Lambda)$

$$
\operatorname{Hom}(P,Ri^!Ri_*Q)\cong\operatorname{Hom}(Ri_!P,Ri_*Q)
=\operatorname{Hom}(Ri_*P,Ri_*Q)\cong\operatorname{Hom}(P,Q),
$$

naturally in $P$, the last step by full faithfulness. Yoneda turns this into
an isomorphism $Ri^!Ri_*Q\cong Q$, and the triangle identities of the
adjunction identify its inverse with $\eta_i^!$.
Source: closed-immersion adjunction in SGA 4, XVII–XVIII.

Uses: `\Cref{sk-def-sf-operations}`, `\Cref{sk-prop-sf-existence}`
