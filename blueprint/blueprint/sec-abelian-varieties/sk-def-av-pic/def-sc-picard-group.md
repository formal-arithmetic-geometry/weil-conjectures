+++
id = "def-sc-picard-group"
kind = "definition"
title = "The Picard group"
lean = ["AlgebraicGeometry.Scheme.Pic"]
order = 443
uses = ["def-sc-curves", "def-sc-invertible-module"]
+++
Let $C$ be a curve. The
*Picard group* $\operatorname{Pic}(C)$ is the set of
isomorphism classes of
invertible $\mathcal O_C$-modules, with the group law induced by tensor product: the
unit is $\mathcal O_C$ and the inverse of an invertible module
$\mathcal L$ is its dual $\mathcal L^{\vee}$. That
$\mathcal L^{\vee}$ is invertible and that this law satisfies
the group axioms is [lem-sc-pic-group], and it is not part of
the definition. (*Stacks Project, Definition 18.32.6, Tag
[040C](https://stacks.math.columbia.edu/tag/040C)*.)
