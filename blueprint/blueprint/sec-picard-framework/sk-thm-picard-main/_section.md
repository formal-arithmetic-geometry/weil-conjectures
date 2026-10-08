+++
id = "sk-thm-picard-main"
kind = "section"
title = "The Picard functor of a smooth projective curve over a separably closed field is representable"
order = 836
uses = ["sk-def-av-jacobian"]
lean = ["AlgebraicGeometry.isRepresentable_picardFunctor"]
+++
*Theorem (sketch).*

(Stacks Project, Proposition 44.6.6, Tag `0B9Z`.)
Let $k$ be a separably closed field and $X$ a smooth projective
curve over $k$. Then the Picard functor $\Pic_{X/k}$ is
representable, and the representing scheme
$\underline{\Pic}_{X/k}$ is a group scheme over $k$.

## Proof

There is a $k$-rational point $\sigma$ ([sk-prop-picard-dense-points]).
By [sk-prop-picard-pic-split] it suffices to represent
$G:=\Pic_{X/k,\sigma}$. We verify the conditions of
[sk-thm-picard-criterion]: (1) $G$ is an fppf, hence Zariski, sheaf
([sk-cor-picard-pic-sheaf]); (2)(a) $F$ is representable
([sk-thm-picard-f-representable]); (2)(b) $F\subseteq G$ is representable
by open immersions ([sk-lem-picard-f-open]); (2)(c) given
$\cL\in G(K)$, [sk-thm-picard-twist] supplies $\cL_0\in G(k)$ with
$h^0=1$ and $H^1=0$ for $\cL_0|_K\otimes\cL$, hence
$Rf_{K,*}(\cL_0|_K\otimes\cL)\cong K[0]$, i.e. $\cL_0\cdot\cL\in F(K)$.
The criterion gives the result, the group structure being the one of
[sk-prop-picard-pic-split].
