+++
id = "lemma-nagata-dense-affine-cover-exists"
kind = "lemma"
title = "Existence of a finite affine cover with dense total intersection"
order = 318
lean = ["AlgebraicGeometry.exists_isAffineOpen_cover_genericPoints_subset", "AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter", "dense_iInf_of_genericPoints_subset"]
uses = ["def-weil-pbc-scheme-conventions", "lem-chow-affine-through-generic-points", "lemma-nagata-affine-neighbourhood-generic-points"]
+++
Let $X$ be quasi-compact and quasi-separated and assume that it has finitely
many irreducible components, with generic points
$\eta_1,\ldots,\eta_r$. There is a finite affine open cover
$(U_1,\ldots,U_n)$ whose total intersection is dense in $X$.

## Proof

For every $x\in X$, apply
[lemma-nagata-affine-neighbourhood-generic-points] to obtain an affine
open containing $x$ and every $\eta_i$. Quasi-compactness gives a finite
subcover. Its total intersection contains the generic point of every
irreducible component, and is therefore dense.

## Detailed form

Let $X$ be a quasi-compact and quasi-separated scheme with finitely many
irreducible components $Z_1,\dots,Z_r$, with generic points $\eta_j$. Then
there is a finite affine open covering $X=U_1\cup\dots\cup U_m$ such that
$\eta_j\in U_i$ for all $i$ and $j$. For any such covering the open

$$
U:=U_1\cap\dots\cap U_m
$$

is dense in $X$.

## Proof

By [lem-chow-affine-through-generic-points] every $x\in X$ has an affine
open neighbourhood containing all the $\eta_j$; since $X$ is quasi-compact,
finitely many of them cover $X$. For the density statement note that
$U\cap Z_j$ is an open subset of $Z_j$ containing $\eta_j$, hence is dense in
the irreducible space $Z_j$; as $X=Z_1\cup\dots\cup Z_r$, the closure of $U$
contains every $Z_j$ and therefore equals $X$.

## Detailed form

Let $X$ be quasi-compact and quasi-separated and assume that $X$ has only
finitely many irreducible components $Z_1,\dots,Z_r$ with generic points
$\eta_j$. Then there is a finite affine open covering

$$
 X=U_1\cup\dots\cup U_m
$$

such that $\eta_j\in U_i$ for every $i,j$. If moreover $X\to Y$ is of finite
type with $Y$ affine, one may take each $U_i$ affine of finite type over $Y$.
In particular the open subscheme $U:=U_1\cap\dots\cap U_m$ is dense in $X$.

## Proof

By [lem-chow-affine-through-generic-points] applied to the finite list
$\eta_1,\dots,\eta_r$, for every $x\in X$ there is an affine open $U_x$
containing $x$ and all the $\eta_j$. Quasi-compactness of $X$ lets us pick a
finite subcover $U_1,\dots,U_m$ among them. If $X\to Y$ is of finite type, an
open subscheme of $X$ is again of finite type over $Y$ (open immersions are of
finite type), so each $U_i$ is affine of finite type over $Y$. Finally $U\cap
Z_j$ is a nonempty open subset of the irreducible space $Z_j$ (it contains
$\eta_j$), hence dense in $Z_j$; since this holds for all $j$ and
$X=Z_1\cup\dots\cup Z_r$, the open $U$ is dense in $X$.
