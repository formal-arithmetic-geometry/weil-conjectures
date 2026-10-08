+++
id = "prop-sf-closed-immersion-unit"
kind = "theorem"
title = "The closed-immersion exceptional unit"
order = 1860
tags = ["latex:proposition"]
uses = ["def-weil-ambient-exceptional-adjoint", "def-weil-exceptional-inverse-image", "def-weil-open-closed-recollement", "def-weil-scheme-morphism-properties", "lem-exc-proetale-closed-exact", "lem-exc-proetale-closed-support", "prop-weil-open-closed-recollement-adjunctions"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $T$ be a Noetherian scheme on which
$\ell$ is invertible (for instance a finite-type scheme over a field in which
$\ell$ is invertible), and let $i:Z\hookrightarrow T$ be a closed immersion
[def-weil-scheme-morphism-properties], with complementary
open immersion $j$, as in the open-closed recollement
[def-weil-open-closed-recollement]. Let $Ri^!$ be the right adjoint of the
direct image $i_*=Ri_*$ on the ambient ordinary derived categories of the
small pro-etale sites, as in [lem-exc-proetale-closed-support]. Then for
every $Q\in D(Z_{\mathrm{proet}},A)$ the adjunction unit is an isomorphism

$$
Q\xrightarrow{\ \eta_i^!\ }Ri^!Ri_*Q .
$$

No boundedness or constructibility of $Q$ is required. In particular, for the
constructible exceptional adjoint $Ri^!$ of
[def-weil-exceptional-inverse-image] — which exists without the ambient datum
of [def-weil-ambient-exceptional-adjoint], that datum being false in general —
computed with the compactification
$Z\xrightarrow{\mathrm{id}}Z\xrightarrow{i}T$ so that $Ri_{!,n}=Ri_*$,
for $Q\in D^b_c(Z,A)$ the unit of the adjunction
$\Hom_T(Ri_!K,L)\cong\Hom_Z(K,Ri^!L)$ of
[def-weil-exceptional-inverse-image] is an isomorphism
$Q\xrightarrow{\sim}Ri^!Ri_*Q$.

## Proof

By [lem-exc-proetale-closed-exact], the closed direct image is exact (the
complement of $Z$ is quasi-compact because $T$ is Noetherian), so $Ri_*$ is
computed by $i_*$ on any complex, and [lem-exc-proetale-closed-support]
provides its right adjoint $Ri^!$ on the ambient derived categories.

By [prop-weil-open-closed-recollement-adjunctions], $i^*\dashv Ri_*$ on the
ambient derived categories and the counit $i^*Ri_*\to\operatorname{id}$ is an
isomorphism. A right adjoint whose counit is an isomorphism is fully
faithful, so for all $P,Q\in D(Z_{\mathrm{proet}},A)$ the map
$g\mapsto Ri_*g$ is a bijection

$$
\Hom(P,Q)\xrightarrow{\ \sim\ }\Hom(Ri_*P,Ri_*Q).
$$

Now fix $Q$ and consider, for every $P$, the composite

$$
\Hom(P,Q)\xrightarrow{\ \eta^!_{i,Q}\circ-\ }\Hom(P,Ri^!Ri_*Q)
\xrightarrow{\ \sim\ }\Hom(Ri_*P,Ri_*Q),
$$

the second map being the adjunction bijection of $Ri_*\dashv Ri^!$. By the
triangle identity, the adjoint of $\eta^!_{i,Q}\circ g$ is
$\epsilon^!_{Ri_*Q}\circ Ri_*(\eta^!_{i,Q})\circ Ri_*g=Ri_*g$, so the
composite is the bijection displayed above. Hence composition with
$\eta^!_{i,Q}$ is a bijection $\Hom(P,Q)\to\Hom(P,Ri^!Ri_*Q)$, naturally in
$P$, and the Yoneda lemma shows that $\eta^!_{i,Q}$ is an isomorphism.

For the last assertion, the right adjoint $Ri_n^{\times}$ of
$Ri_{!,n}=Ri_*$ given by the datum of [def-weil-ambient-exceptional-adjoint]
is, by uniqueness of right adjoints, identified with $Ri^!$ together with its
unit. The functor $Ri^!$ of [def-weil-exceptional-inverse-image] is its
restriction to $D^b_c$, with the same unit, so its unit at $Q\in D^b_c(Z,A)$
is the isomorphism just proved.
