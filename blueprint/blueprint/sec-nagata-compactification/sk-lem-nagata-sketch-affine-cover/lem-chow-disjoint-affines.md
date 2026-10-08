+++
id = "lem-chow-disjoint-affines"
kind = "lemma"
title = "Disjoint affine neighbourhoods of generic points"
order = 316
lean = ["AlgebraicGeometry.exists_isAffineOpen_of_subset_genericPoints", "AlgebraicGeometry.exists_isAffineOpen_pairwise_disjoint"]
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $X$ be a quasi-separated scheme, let $Z_1,\dots,Z_n$ be pairwise distinct
irreducible components of $X$ and let $\eta_i\in Z_i$ be their generic points.
Then there are affine opens $U_i\subseteq X$ with $\eta_i\in U_i$ and
$U_i\cap U_j=\emptyset$ for $i\neq j$. Consequently
$U_1\cup\dots\cup U_n$ is an affine open containing all the $\eta_i$.

## Proof

For $k\neq i$ we have $\eta_i\notin Z_k$: otherwise
$Z_i=\overline{\{\eta_i\}}\subseteq Z_k$, contradicting that $Z_i$ and $Z_k$
are distinct irreducible components. Hence
$\bigcap_{k\neq i}(X\setminus Z_k)$ is an open neighbourhood of $\eta_i$, and
since the affine opens form a basis of the topology we may choose an affine
open $V_i$ with

$$
\eta_i\in V_i\subseteq\bigcap_{k\neq i}(X\setminus Z_k).
$$

In particular $V_i\cap Z_k=\emptyset$, and a fortiori $\eta_k\notin V_i$, for
all $k\neq i$.

Fix $i$ and put $W_i:=\bigcup_{j\neq i}(V_i\cap V_j)$. Each $V_i\cap V_j$ is
quasi-compact because $X$ is quasi-separated, so $W_i$ is a quasi-compact open
subset of $V_i$, and $\eta_i\notin W_i$ because $\eta_i\notin V_j$ for
$j\neq i$. Write $V_i=\Spec R_i$. The irreducible components of the open
subscheme $V_i$ are the nonempty intersections $C\cap V_i$ with $C$ an
irreducible component of $X$, so $Z_i\cap V_i$ is an irreducible component of
$V_i$ with generic point $\eta_i$; equivalently $\eta_i$ corresponds to a
minimal prime $\mathfrak p_i\subseteq R_i$. By 00EV applied to
$R_i$, the minimal prime $\mathfrak p_i$ and the quasi-compact open
$W_i\subseteq\Spec R_i$, there is $f_i\in R_i\setminus\mathfrak p_i$ with
$D(f_i)\cap W_i=\emptyset$. Put $U_i:=D(f_i)$. Then $U_i$ is an affine open
containing $\eta_i$, and for $j\neq i$ we have
$U_i\cap V_j\subseteq V_i\cap V_j\subseteq W_i$, whence
$U_i\cap V_j=\emptyset$ and in particular $U_i\cap U_j=\emptyset$.

Finally, a scheme that is the disjoint union of two affine opens is affine by
01I5; iterating, $U_1\cup\dots\cup U_n$ is affine.

## Detailed form

Let $X$ be quasi-separated, let $Z_1,\dots,Z_n$ be pairwise distinct
irreducible components of $X$, and let $\eta_i\in Z_i$ be their generic
points. Then for every $i$ there is an affine open $V_i\subseteq X$ containing
$\eta_i$ such that $V_i\cap Z_k=\emptyset$ for $k\neq i$; in particular the
$V_i$ are pairwise disjoint.
(Stacks Project, Properties, Tag
[01ZV](https://stacks.math.columbia.edu/tag/01ZV) = Lemma 28.30.1.)

## Proof

For $k\neq i$ the point $\eta_i$ does not lie in the closed set $Z_k$, since
the $Z_l$ are pairwise distinct irreducible components and $\eta_i\in Z_i$;
hence $X\setminus Z_k$ is an open neighbourhood of $\eta_i$, as is the finite
intersection

$$
 W_i:=\bigcap_{k\neq i}(X\setminus Z_k),
$$

which satisfies $W_i\cap Z_k=\emptyset$ for all $k\neq i$. The affine open
subschemes of a scheme form a basis for its topology (every scheme is locally
$\operatorname{Spec}$ of a ring, in which the distinguished opens form a
basis), so there is an affine open $V_i$ with $\eta_i\in V_i\subseteq W_i$;
this gives $V_i\cap Z_k=\emptyset$ for $k\neq i$. For $i\neq j$ the open set
$V_i$ avoids $Z_j$, whereas $V_j\ni\eta_j\in Z_j$, so $V_i\cap V_j=\emptyset$,
i.e. the $V_i$ are pairwise disjoint.
