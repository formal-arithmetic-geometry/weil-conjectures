+++
id = "thm-pc-picard-representable"
kind = "theorem"
title = "The Picard scheme of a curve is representable"
order = 837
uses = ["cor-pc-sigma-pic-iso", "def-pc-genus", "def-pc-pic-sigma-functor", "def-pc-picard-functor", "def-pc-separably-closed", "def-pc-smooth-projective-curve", "def-pc-subfunctor", "lem-pc-f-open-subfunctor", "lem-pc-k-sheaf", "lem-pc-rational-hyp", "lem-pc-rational-points-dense", "lem-pc-sigma-k-points", "lem-pc-twist", "lem-pc-vanishing-above-dim", "lem-pc-zariski-coverings-are-fppf", "prop-pc-xk-integral", "thm-pc-criterion", "thm-pc-f-representable", "thm-pc-pic-split"]
lean = ["AlgebraicGeometry.isRepresentable_picardFunctor"]
+++
(Stacks Project, Picard Schemes of Curves, Proposition 44.6.6, Tag
[0B9Z](https://stacks.math.columbia.edu/tag/0B9Z).)
Let $k$ be a separably closed field.
Let $X$ be a
smooth projective curve over
$k$. Then the
Picard functor $\operatorname{Pic}_{X/k}$ is
representable, and the representing scheme
$\underline{\operatorname{Pic}}_{X/k}$ is a group scheme over $k$.

## Proof

Since $k$ is separably closed and $X$ is smooth over $k$ (hence nonempty:
$X$ is a variety), there exists a
$k$-rational point $\sigma$ of $X$ by
[lem-pc-rational-points-dense]. By [cor-pc-sigma-pic-iso] it
suffices to show that the functor
$\operatorname{Pic}_{X/k,\sigma}$ classifying invertible modules trivial along
$\sigma$ is representable (then $\operatorname{Pic}_{X/k}$ is representable too, and
the representing scheme carries the group structure because it represents
the group-valued functor; moreover the fact that it is a group scheme
follows from the conclusion of [thm-pc-criterion]).

We check the conditions (1), (2)(a), (2)(b), (2)(c) of
[thm-pc-criterion] (with $G=\operatorname{Pic}_{X/k,\sigma}$ and $F$ the
subfunctor of [lem-pc-f-open-subfunctor]):

1. **(1)** The functor $\operatorname{Pic}_{X/k,\sigma}$ satisfies the sheaf condition
for the fppf topology: by [lem-pc-rational-hyp] the hypotheses of
[thm-pc-pic-split] hold, and the fppf sheaf condition for
$K=\operatorname{Pic}_{X/k,\sigma}$ was shown in
[lem-pc-k-sheaf]. Since every Zariski covering is an fppf covering ([lem-pc-zariski-coverings-are-fppf])
(affine-locally the maps $\operatorname{Spec}(A_f)\to\operatorname{Spec}(A)$ are flat and of finite
presentation, $A\to A_f$ being the localization), it satisfies the sheaf
property for the Zariski topology. [Condition (1); note that
[cor-pc-sigma-pic-iso] gives the same conclusion from the fact that
$\operatorname{Pic}_{X/k}$ is by definition an fppf sheaf.]
1. **(2)(a)** The subfunctor $F$ of [lem-pc-f-open-subfunctor] is
representable: [thm-pc-f-representable] represents it by the open
subscheme $W\subseteq\underline{\operatorname{Hilb}}^g_{X/k}$ (the genus $g$ is finite:
$X$ is a smooth projective curve over $k$, geometrically irreducible by
[prop-pc-xk-integral], so [def-pc-genus] applies).
1. **(2)(b)** $F\subseteq\operatorname{Pic}_{X/k,\sigma}$ is representable by open
immersions: [lem-pc-f-open-subfunctor].
1. **(2)(c)** Let $K/k$ be a field extension and let
$g_0\in\operatorname{Pic}_{X/k,\sigma}(K)$, i.e. an invertible module $\mathcal{L}$ on $X_K$
with $\sigma_K^*\mathcal{L}\cong\mathcal{O}_K$. By [lem-pc-twist] there is an
invertible sheaf $\mathcal{L}_0$ on $X$ with
$\dim_KH^0(X_K,\mathcal{L}\otimes\mathcal{L}_0|_{X_K})=1$ and
$H^1(X_K,\mathcal{L}\otimes\mathcal{L}_0|_{X_K})=0$. Since
$\operatorname{Pic}_{X/k,\sigma}(k)=\operatorname{Pic}(X)$ ([def-pc-pic-sigma-functor], [lem-pc-sigma-k-points]), the
module $\mathcal{L}_0$ corresponds to an element $g_0'\in G(k)$; and in
$G(K)$ the product $g_0'\cdot g_0$ is the class of
$\mathcal{L}_0|_{X_K}\otimes\mathcal{L}$. For it we have
$H^p(X_K,\cdot)=0$ for all $p\geq1$
(Serre: from [lem-pc-twist] we have $H^1=0$ and
[lem-pc-vanishing-above-dim] gives $H^p=0$ for $p\geq2$), and
$H^0$ is $1$-dimensional over $K$, so
$$
Rf_{K,*}\bigl(\mathcal{L}_0|_{X_K}\otimes\mathcal{L}\bigr)\cong\bigl(H^0(X_K,\mathcal{L}_0|_{X_K}\otimes\mathcal{L})\bigr)[0]
\cong K[0],
$$
which is an invertible $\mathcal{O}_K$-module placed in degree $0$; hence
$g_0'g_0\in F(K)$ as required.

All four conditions hold, so by [thm-pc-criterion] the functor
$\operatorname{Pic}_{X/k,\sigma}$ is representable by a group scheme over $k$, and
hence so is $\operatorname{Pic}_{X/k}$ by [cor-pc-sigma-pic-iso].
