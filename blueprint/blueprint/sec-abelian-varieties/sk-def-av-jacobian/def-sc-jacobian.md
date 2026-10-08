+++
id = "def-sc-jacobian"
kind = "definition"
title = "The Jacobian"
lean = ["AlgebraicGeometry.IsJacobian"]
order = 464
uses = ["def-sc-abelian-variety", "def-sc-general-curve", "def-sc-pic0", "def-sc-picard-functor"]
+++
Let $C$ be a geometrically integral smooth
projective curve over a field $k$, of genus $g=g(C)$
([def-sc-general-curve]). A
*Jacobian of $C$* is a pair $(J,\varphi)$ consisting of an
abelian variety $J$ over $k$
of dimension $g$ together with an isomorphism of group-valued
functors

$$
\varphi:\operatorname{Pic}^0_{C/k}\xrightarrow{\ \sim\ }h_J,
$$

where $\operatorname{Pic}^0_{C/k}$ is the degree-zero part of the
Picard functor
([def-sc-pic0], [def-sc-picard-functor]); that is, a
Jacobian of $C$ is a representing object of
$\operatorname{Pic}^0_{C/k}$ in the category of abelian varieties
of dimension $g$ over $k$, together with the representing
isomorphism. Whether such a pair exists, and which properties it
has, is not part of this definition. When a Jacobian
$(J,\varphi)$ of $C$ is fixed, we write $J_C:=J$ and call
$J_C$ the *Jacobian* of $C$, so that $\varphi$ is the
canonical identification $\operatorname{Pic}^0_{C/k}\cong h_{J_C}$.
