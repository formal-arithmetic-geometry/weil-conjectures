+++
id = "sk-i-real-galois"
kind = "section"
title = "Galois correspondence for finite local systems"
order = 2580
uses = ["sk-d-real-setup"]
lean = ["AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf", "Rep.IsFiniteContinuous"]
+++
*Proposition (sketch).*

Let $Y$ be a connected scheme with geometric point $\bar y$ and let
$\Lambda$ be a finite ring. Write $\mathrm{F\acute Et}(Y)$ for the category
of finite etale covers of $Y$, $F_{\bar y}$ for the fiber functor sending a
cover to its finite fiber at $\bar y$, and
$\pi_1(Y,\bar y)=\operatorname{Aut}(F_{\bar y})$ with its profinite topology.
A sheaf of finite $\Lambda$-modules on $Y_\Et$ is locally constant if it
becomes constant on an etale covering.

The geometric-stalk functor is an exact tensor equivalence between locally
constant sheaves of finite $\Lambda$-modules on $Y_\Et$ and finite
$\Lambda$-modules carrying a continuous action of $\pi_1(Y,\bar y)$,
compatibly with base change along a map $\Lambda\to\Lambda'$ of finite rings.

## Proof

*Sheaves and covers.* The functor $P\mapsto\underline{\operatorname{Hom}}_Y(-,P)$
from finite etale covers to finite locally constant sheaves of sets is an
equivalence. A finite etale cover is trivial after an etale base change, so
its sheaf of sections is locally constant with finite fibers. It is fully
faithful because a morphism of covers is determined by its graph, a closed
subscheme and hence a subsheaf, and every map of sheaves descends from a map
of finite sets over a common trivializing cover. It is essentially surjective
because the glueing data of a locally constant sheaf transport to a descent
datum for a trivial cover, which is effective for finite etale morphisms.

*Covers and $\pi_1$-sets.* For connected $Y$ the Galois covers are
cofinal among connected covers and pro-represent $F_{\bar y}$, so
$\pi_1(Y,\bar y)$ is profinite and acts continuously on every fiber, with open
stabilizers; the action is transitive on a connected cover. Hence
$F_{\bar y}$ is an equivalence onto finite continuous $\pi_1(Y,\bar y)$-sets,
compatibly with finite limits and colimits.

*Linear structure.* A $\Lambda$-module structure on a locally constant
sheaf is a $\Lambda$-action on the corresponding object, carried by both
equivalences; composing them gives the geometric-stalk functor of the
statement.

*Exactness, tensor and coefficients.* Two locally constant sheaves
become constant on a common etale covering, on which a map between them is a
map of constant sheaves; its kernel and cokernel are therefore again locally
constant, and are computed on stalks, so the equivalence is exact. The same
common covering computes $\otimes_\Lambda$ and the base change
$-\otimes_\Lambda\Lambda'$ stalkwise, giving the remaining two compatibilities.

Uses: [sk-d-real-setup]
