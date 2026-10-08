+++
id = "prop-weil-localized-tstructure"
kind = "theorem"
title = "The rational t-structure"
order = 1432
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-pbc-bounded-constructible-complete", "def-weil-pbc-rational-category", "def-weil-t-structure", "prop-weil-pbc-integral-tstructure", "thm-weil-pbc-integral-truncations"]
tags = ["latex:proposition"]
+++
Let $E/\Ql$ be finite and let $\varpi$ be a uniformizer of $\mathcal O_E$.
By [prop-weil-pbc-integral-tstructure] the standard t-structure restricts to
$\Dbc(T,\mathcal O_E)$ [def-weil-pbc-bounded-constructible-complete], and
the $\varpi$-power-torsion subcategory is stable under the truncation
functors; the truncations are the levelwise ones on the reduction tower
[thm-weil-pbc-integral-truncations], which is exactly the adic-model
condition of the standard t-structure (objectwise cohomological boundedness
alone is not a bounded t-structure on a derived-complete category, and the
levelwise definition shows the truncations to persist). Then the
subcategories
$$
  (\Dbc(T,E))^{\le0}:=
  \{K:K\cong L\text{ in }\Dbc(T,E),\ L\in(\Dbc(T,\mathcal O_E))^{\le0}\},
$$
$$
  (\Dbc(T,E))^{\ge0}:=
  \{K:K\cong L\text{ in }\Dbc(T,E),\ L\in(\Dbc(T,\mathcal O_E))^{\ge0}\},
$$
with the objects of $\Dbc(T,E)$ [def-weil-pbc-rational-category] identified
with those of $\Dbc(T,\mathcal O_E)$, form a bounded t-structure on
$\Dbc(T,E)$ for which the localization functor is t-exact; the truncation
functors are the levelwise canonical truncations on an integral
representative, and the heart is the essential image of the integral heart.

*Source note:* no Stacks Project entry states this form: Stacks has no
t-structure or heart, and its truncation entries (Homological Algebra,
Section 12.15, [Tag 0118](https://stacks.math.columbia.edu/tag/0118); Remark
13.12.4, [Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)) concern the
complexes of one fixed abelian category and are not stable under changing
the coefficient ring; the blueprint adds the bounded t-structure on the
rational category $\Dbc(T,E)$, its $t$-exactness for the localization
functor and the identification of its heart with the integral heart.

## Proof

The shift conditions hold first for the integral representatives in
$\Dbc(T,\mathcal O_E)$, by [prop-weil-pbc-integral-tstructure], and then for
their isomorphism closures in the rational category. For orthogonality,
choose integral representatives $A_0$ in degrees $\le0$ and $B_0$ in degrees
$\ge0$, together with rational isomorphisms $A\cong A_0$ and $B\cong B_0$.
By [def-weil-pbc-rational-category],
$$
 \Hom_{\Dbc(T,E)}(A,B[-1])
  \cong\Hom_{\Dbc(T,\mathcal O_E)}(A_0,B_0[-1])\otimes_{\mathcal O_E}E=0,
$$
the first factor being zero by orthogonality of
[prop-weil-pbc-integral-tstructure] and the tensor product being zero. For
the truncation axiom, the truncation triangle
$$
 \tau^{\le0}K\longrightarrow K\longrightarrow\tau^{\ge1}K
 \longrightarrow\tau^{\le0}K[1]
$$
of $K$ in $\Dbc(T,\mathcal O_E)$ (the triangle of
[thm-weil-pbc-integral-truncations] (iii)) is carried to a distinguished
triangle of $\Dbc(T,E)$ by the exact localization functor of
[def-weil-pbc-rational-category], whose end terms lie in
$(\Dbc(T,E))^{\le0}$ and $(\Dbc(T,E))^{\ge0}$ by definition; the same
argument at every truncation level shows that the truncations are computed
levelwise on integral representatives. Boundedness, in terms of the
cohomology sheaves, is inherited: an object of $\Dbc(T,E)$ is an object of
the bounded category $\Dbc(T,\mathcal O_E)$. The t-exactness of the
localization functor is the identity on objects together with the displayed
definitions of the two subcategories, and the heart is the essential image
in $\Dbc(T,E)$ of the integral heart.

The source records that audit item BC-03 is resolved for this proposition:
its truncation functors are those of [thm-weil-pbc-integral-truncations],
whose proof is complete once the Tor-compatibility condition is carried as
an explicit hypothesis.
