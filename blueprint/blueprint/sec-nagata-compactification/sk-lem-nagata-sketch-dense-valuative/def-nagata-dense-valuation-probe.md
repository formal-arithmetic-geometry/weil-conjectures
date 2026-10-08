+++
id = "def-nagata-dense-valuation-probe"
kind = "definition"
title = "Valuation probe through a schematically dense source"
order = 279
lean = ["AlgebraicGeometry.ValuativeCommSqWithPt", "AlgebraicGeometry.ValuativeCommSqWithPt.ofIsDominant"]
uses = ["def-nagata-scheme-theoretic-image"]
+++
Let $h\colon T\to P$ be quasi-compact, assume its image
inclusion $\operatorname{SIm}(h)\hookrightarrow P$ is an isomorphism, assume
$P$ is affine, and let $z\in P$.
Select a witness from
[def-nagata-dense-valuation-probe] and denote it by

$$
\mathsf{VP}(h,z)=
(A'_{h,z},K'_{h,z},\eta_{h,z},\alpha_{h,z}),
$$

where $A'_{h,z}$ is the selected valuation ring, $K'_{h,z}$ its fraction
field, $\eta_{h,z}\colon\operatorname{Spec}(K'_{h,z})\to T$ the selected
generic lift, and
$\alpha_{h,z}\colon\operatorname{Spec}(A'_{h,z})\to P$ the selected centred
valuation map.

## Existence of a valuation probe through a dense source

Let $h\colon T\to P$ be quasi-compact, assume its image
inclusion $\operatorname{SIm}(h)\hookrightarrow P$ is an isomorphism, assume
$P$ is affine, and let $z\in P$. There
exist a valuation ring $A'$ with fraction field $K'$, a morphism
$\eta\colon\operatorname{Spec}(K')\to T$, and a morphism
$\alpha\colon\operatorname{Spec}(A')\to P$ such that the generic square
commutes and the closed point of $\operatorname{Spec}(A')$ maps to $z$.

*Proof.*
Let $Z=\operatorname{SIm}(h)$. The assumed image isomorphism identifies
$z$ with a point of $Z$. Stacks Project, Tag 02JQ (Lemma 29.6.5),
applied to the quasi-compact morphism $h$ and the point $z\in Z$, supplies
a valuation ring $A'$, its fraction field $K'$, a map
$\operatorname{Spec}(K')\to T$, and a map
$\operatorname{Spec}(A')\to Z$ whose generic restriction is the supplied
map and whose closed point is $z$. Composing the latter map with the image
closed immersion $Z\hookrightarrow P$ gives $\alpha$, and the generic
commutativity supplied by the theorem is exactly the displayed square.
