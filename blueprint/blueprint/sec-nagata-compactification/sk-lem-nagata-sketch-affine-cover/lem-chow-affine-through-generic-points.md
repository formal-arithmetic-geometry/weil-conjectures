+++
id = "lem-chow-affine-through-generic-points"
kind = "lemma"
title = "An affine open containing a point and all generic points"
order = 317
lean = ["AlgebraicGeometry.exists_isAffineOpen_mem_of_subset_genericPoints"]
uses = ["def-weil-pbc-scheme-conventions", "lem-chow-disjoint-affines"]
+++
Let $X$ be a quasi-separated scheme, let $Z_1,\dots,Z_n$ be pairwise distinct
irreducible components of $X$ with generic points $\eta_i$, and let $x\in X$.
Then there is an affine open $U\subseteq X$ containing $x$ and all the
$\eta_i$.

## Proof

After renumbering we may assume $x\in Z_i$ for $i\leq r$ and $x\notin Z_k$ for
$k>r$. Then $\bigcap_{k>r}(X\setminus Z_k)$ is an open neighbourhood of $x$,
so there is an affine open $W$ with
$x\in W\subseteq\bigcap_{k>r}(X\setminus Z_k)$; thus $W\cap Z_k=\emptyset$ for
$k>r$. For $i\leq r$ the set $W\cap Z_i$ is a nonempty open subset of the
irreducible space $Z_i$, hence contains its generic point, so $\eta_i\in W$.

By [lem-chow-disjoint-affines] applied to $Z_{r+1},\dots,Z_n$ there are
pairwise disjoint affine opens $U_k\ni\eta_k$ for $k>r$. Fix $k>r$. Since $X$
is quasi-separated, $W\cap U_k$ is a quasi-compact open of $U_k$, and it does
not contain $\eta_k$ because $\eta_k\in Z_k$ while $W\cap Z_k=\emptyset$. As
in the proof of [lem-chow-disjoint-affines], $\eta_k$ is a minimal prime
of the affine scheme $U_k$, so 00EV provides a standard affine
open $U_k'\subseteq U_k$ with $\eta_k\in U_k'$ and $U_k'\cap W=\emptyset$.

The opens $W$ and $U_k'$ for $k>r$ are pairwise disjoint and affine, so

$$
U:=W\cup\bigcup_{k>r}U_k'
$$

is affine by 01I5, and it contains $x$ and all the $\eta_i$.

## Detailed form

Let $X$ be quasi-separated, let $Z_1,\dots,Z_n$ be pairwise distinct
irreducible components of $X$ with generic points $\eta_i$, and let $x\in X$.
Then there is an affine open $U\subseteq X$ containing $x$ and all the
$\eta_i$.
(Stacks Project, Properties, Tag
[01ZX](https://stacks.math.columbia.edu/tag/01ZX) = Lemma 28.30.4.)

## Proof

After renumbering, let $x\in Z_i$ precisely for $i\leq r$, so that $x\notin
Z_k$ for $k>r$.

*Step 1: an affine open $W$ around $x$ avoiding the components not through
$x$.* For $k>r$, the complement $X\setminus Z_k$ is an open neighbourhood of
$x$, hence so is the finite intersection $O:=\bigcap_{k>r}(X\setminus Z_k)$.
Since the affine open subschemes form a basis of the topology, we may choose
an affine open $W$ with $x\in W\subseteq O$; then $W\cap Z_k=\emptyset$ for
$k>r$.

*Step 2: the generic points $\eta_i$, $i\leq r$, lie in $W$.* For $i\leq r$
the intersection $W\cap Z_i$ is nonempty (it contains $x$) and is an open
subset of the irreducible space $Z_i$; every nonempty open subset of an
irreducible space contains its generic point, so $\eta_i\in W\cap Z_i\subseteq
W$.

*Step 3: disjoint affine opens around $\eta_{r+1},\dots,\eta_n$.* Apply
[lem-chow-disjoint-affines] to the components
$Z_{r+1},\dots,Z_n$: for every $k>r$ there is an affine open $V_k\ni\eta_k$
with $V_k\cap Z_l=\emptyset$ for $l>r,\ l\neq k$, and the $V_k$ are pairwise
disjoint.

*Step 4: shrinking the $V_k$ away from $W$.* Let $k>r$. Quasi-separatedness of
$X$ means that the diagonal $X\to X\times_{\mathbf Z}X$ is quasi-compact; the
open $W\cap V_k$ is the base change of the diagonal along $W\times_{\mathbf
Z}V_k\to X\times_{\mathbf Z}X$, so $W\cap V_k\to W\times_{\mathbf Z}V_k$ is
quasi-compact, and the target is affine, whence $W\cap V_k$ is quasi-compact.
Writing $V_k=\operatorname{Spec}R_k$, the point $\eta_k$ corresponds to a
minimal prime $\mathfrak p_k$ of $R_k$: indeed $Z_k\cap V_k$ is an irreducible
component of $V_k$ (otherwise its closure in $X$ would contain a closed
irreducible subset strictly larger than $Z_k$), and it is the closure of
$\{\eta_k\}$, so $\mathfrak p_k$ is a minimal prime. By Algebra, Lemma 10.26.4
(Stacks Project, Tag [00EV](https://stacks.math.columbia.edu/tag/00EV)),
applied to $R:=R_k$, the minimal prime $\mathfrak p_k$, and the quasi-compact
open $W\cap V_k\subseteq\operatorname{Spec}R_k$ which does not contain
$\mathfrak p_k$ (as $W\cap Z_k=\emptyset$), there is $f_k\in
R_k\setminus\mathfrak p_k$ with $D(f_k)\cap(W\cap V_k)=\emptyset$. Put
$V_k':=D(f_k)\subseteq V_k$: this is an affine open containing $\eta_k$ and
disjoint from $W$.

*Step 5: the union.* The opens $W$ and $V_k'$ ($k>r$) are pairwise disjoint
and each is affine, so their union

$$
 U:=W\cup\bigcup_{k>r}V_k'
$$

is affine: by Schemes, Lemma 26.6.8 (Tag
[01I5](https://stacks.math.columbia.edu/tag/01I5)) a disjoint union of two
affine opens is affine, and we iterate. It contains $x$ and all
$\eta_1,\dots,\eta_n$, as required.
