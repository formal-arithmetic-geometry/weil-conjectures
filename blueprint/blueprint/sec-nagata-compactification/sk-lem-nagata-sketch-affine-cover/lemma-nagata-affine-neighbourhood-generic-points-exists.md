+++
id = "lemma-nagata-affine-neighbourhood-generic-points-exists"
kind = "lemma"
title = "Existence of an affine neighbourhood through finitely many generic points, [stacks-project]"
order = 313
+++
**Status.** Bypassed by the formalized route: the affine cover meeting the
selected generic points is produced in one step by
`AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter`
and `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter`.

Let $X$ be quasi-separated, let $x\in X$, and let
$\eta_1,\ldots,\eta_r$ be generic points of finitely many distinct
irreducible components. There is an affine open of $X$ containing $x$ and
every $\eta_i$.

## Proof

Reorder the components so that
$x\in Z_1\cap\cdots\cap Z_m$ and
$x\notin Z_{m+1},\ldots,Z_r$, where $Z_i$ is the component with generic
point $\eta_i$. Choose an affine open $W$ containing $x$ and disjoint from
$Z_{m+1},\ldots,Z_r$. Then $W$ contains
$\eta_1,\ldots,\eta_m$. By Stacks Project, Tag 01ZV, choose pairwise
disjoint affine opens $A_i$ containing $\eta_i$ for $i>m$. Since $X$ is
quasi-separated, each $W\cap A_i$ is quasi-compact; it does not contain
$\eta_i$. Write $A_i=\operatorname{Spec}(R_i)$ and let
$\mathfrak p_i$ be the minimal prime corresponding to $\eta_i$. Stacks
Project, Tag 00EV, applied to $W\cap A_i$ gives
$f_i\in R_i\setminus\mathfrak p_i$ such that
$D(f_i)\cap W=\varnothing$. Replace $A_i$ by $D(f_i)$. It still contains
$\eta_i$, remains disjoint from the other $A_j$, and is disjoint from $W$.
Thus

$$
W\amalg A_{m+1}\amalg\cdots\amalg A_r
$$

is a finite disjoint union of affine schemes, hence is affine, and it
contains $x$ and every selected generic point. This is the construction in
Stacks Project, Tag 01ZX.
