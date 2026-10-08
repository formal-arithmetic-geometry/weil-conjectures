+++
id = "cor-pd-finite-level"
kind = "theorem"
title = "The descent datum is defined at a finite separable level"
order = 863
tags = ["latex:corollary"]
uses = ["def-pc-base-change", "def-pc-geometrically-irreducible", "def-pc-morphism-conventions", "def-pc-projective-morphism", "def-pc-smooth-projective-curve", "def-pd-descent-datum", "def-pd-separable-closure", "lem-pd-canonical-descent-datum", "lem-pd-descent-cocycle", "lem-sc-abelian-variety-projective", "thm-pd-geometric-pic0", "thm-pd-spreading-out"]
+++
Let $k$ be a field, let $C$ be a
smooth projective curve over $k$
which is geometrically integral,
and let $(J_s,\varphi)$ be the scheme with its
descent datum furnished by
[lem-pd-canonical-descent-datum] and [lem-pd-descent-cocycle]. Then
there are a finite separable extension $K/k$, a scheme $J_K$ of finite
presentation over $K$, and a descent datum
$\varphi_K$ on $J_K$ over $\Spec(K)/\Spec(k)$ such that
$J_K\times_KK_s\cong J_s$ and such that $\varphi_K$
base changes to $\varphi$; moreover $J_K$ may
be chosen projective over $K$.

## Proof

The datum $(J_s,\varphi)$ of [lem-pd-canonical-descent-datum] and
[lem-pd-descent-cocycle] is a
[def-pd-descent-datum] over $\Spec(k_s)/\Spec(k)$ with $k_s$ the
[def-pd-separable-closure]. Write
$k_s=\colim_{K/k\ \text{finite separable}}K$ and $S_i=\Spec(K_i)$ for the
finite separable subextensions, an inverse system with affine transition
morphisms and affine (hence quasi-compact and quasi-separated) terms, whose
limit is $S=\Spec(k_s)$; all fibre products below are the finite-presentation
ones of [def-pc-morphism-conventions]. The scheme $J_s$ is of finite
presentation over $k_s$: it is smooth over the field $k_s$ and of finite type,
by [thm-pd-geometric-pic0]. By
[thm-pd-spreading-out](1) there are $i$ and a scheme $J_i$ of finite
presentation over $K_i$ with $J_i\times_{K_i}k_s\cong J_s$; enlarge $i$ if
necessary so that the $\varphi$ and the cocycle equation, which are morphisms
and equalities of morphisms of finite presentation between finitely presented
schemes, spread out as well, using [thm-pd-spreading-out](2) and
[thm-pd-spreading-out](3); the spread-out isomorphism is the descent
datum $\varphi_K$ over $\Spec(K)/\Spec(k)$, whose base change to $\Spec(k_s)$
is $\varphi$ by the very form of [def-pc-base-change]. To obtain
projectivity, apply [thm-pd-spreading-out](2) to a closed immersion
$J_s\hookrightarrow\mathbf{P}^N_{k_s}$, which exists because $J_s$ is an
abelian variety by [thm-pd-geometric-pic0] and abelian varieties are
projective by [lem-sc-abelian-variety-projective]; the target
$\mathbf{P}^N_{k_s}$ is the base change of $\mathbf{P}^N_{K_i}$, so the
immersion descends to a closed immersion $J_{i'}\hookrightarrow \mathbf{P}^N_{K_{i'}}$ for some $i'\geq i$, exhibiting $J_{i'}$ as a
[def-pc-projective-morphism] over $K_{i'}$. Put
$K=K_{i'}$ and $J_K=J_{i'}$.
