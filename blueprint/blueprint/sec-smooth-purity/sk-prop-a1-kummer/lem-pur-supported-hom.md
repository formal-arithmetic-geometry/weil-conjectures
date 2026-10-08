+++
id = "lem-pur-supported-hom"
kind = "lemma"
title = "Supported cohomology as morphisms"
order = 1940
uses = ["def-pur-flasque-support", "def-pur-support-cohomology", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-scheme-morphism-properties"]
+++
Let $i:Z\hookrightarrow X$ be a
closed immersion and
let $F$ be a bounded below complex of coefficient sheaves on $X$.
The supported cohomology group
has a natural identification

$$
H^a_Z(X,F)=\operatorname{Hom}_{D(X,\Lambda)}(i_*\Lambda_Z,F[a]).
$$

## Proof

For an injective resolution $F\to I$, the identity
$\Gamma_Z(X,I)=\Gamma(Z,i^!I)$ follows from
[def-pur-flasque-support]. Its derived version identifies
$H_Z^a(X,F)$ of [def-pur-support-cohomology] with
$\operatorname{Hom}_{D(Z)}(\Lambda_Z,Ri^!F[a])$: global sections
are Hom from the coefficient unit, by
[def-weil-derived-pullback-tensor-hom].
The adjunction $i_*\dashv Ri^!$ of
[def-weil-exceptional-inverse-image] gives the displayed group.
