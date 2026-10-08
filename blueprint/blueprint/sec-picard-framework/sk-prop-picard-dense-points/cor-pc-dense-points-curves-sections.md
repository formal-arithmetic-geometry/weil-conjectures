+++
id = "cor-pc-dense-points-curves-sections"
kind = "theorem"
title = "Consequences of the density of rational points"
order = 753
tags = ["latex:corollary"]
uses = ["def-pc-curve", "def-pc-separably-closed", "def-pc-smooth-projective-curve", "def-sc-invertible-module", "lem-pc-rational-points-dense"]
+++
Let $k$ be a separably closed field and let $X$ be a scheme over $k$
which is smooth over $k$.

1. For every field extension $K/k$ put $X_K=X\times_{\operatorname{Spec}k}\operatorname{Spec}K$, and for
$x\in X(k)$ let $x_K=\operatorname{Spec}(K)\times_kx$ be the induced $K$-rational point of
$X_K$. Then the set $\{x_K : x\in X(k)\}$ is Zariski dense in $X_K$ (for $K=k$
this is the density of $X(k)$ in $X$).
1. Let $\mathcal{L}$ be an invertible $\mathcal{O}_{X_K}$-module and
$s\in H^0(X_K,\mathcal{L})$ a section which does not vanish identically, i.e.
$s(y)\neq0$ in $\mathcal{L}(y)=\mathcal{L}_y\otimes\kappa(y)$ for some $y\in X_K$.
Then there is an $x\in X(k)$ such that $s$ does not vanish at $x_K$.
1. If $X$ is a smooth projective curve over $k$, then $X(k)$ is infinite.
If moreover $K=k$, then every non-zero $s\in H^0(X,\mathcal{L})$, for $\mathcal{L}$ an
invertible $\mathcal{O}_X$-module, does not vanish identically, so (2) applies:
$s(x)\neq0$ for some $x\in X(k)$.

## Proof

(1) Let $p:X_K\to X$ be the projection. It is the base change of
$\operatorname{Spec}K\to\operatorname{Spec}k$ along $X\to\operatorname{Spec}k$, and the structure morphism of any
scheme over a field is universally open (Morphisms of Schemes,
Lemma 29.23.4, Tag [0383](https://stacks.math.columbia.edu/tag/0383));
hence $p$ is open. Let $Z\subseteq X_K$ be a closed subset containing every
$x_K$, and suppose $U:=X_K\setminus Z\neq\emptyset$. Then $p(U)\subseteq X$ is a
nonempty open subset, so by [lem-pc-rational-points-dense] it contains a
point $x\in X(k)$. The fibre of $p$ over $x$ is
$\operatorname{Spec}(\kappa(x)\otimes_kK)=\operatorname{Spec}(k\otimes_kK)=\operatorname{Spec}K$, a single point, namely
$x_K$. Since $x\in p(U)$, some point of $U$ lies over $x$, so $x_K\in U$,
contradicting $x_K\in Z$. Hence $Z=X_K$, which is the asserted density.

(2) The set $W:=\{y\in X_K : s(y)\neq0\}$ is open: on an open
$V=\operatorname{Spec}A\subseteq X_K$ on which $\mathcal{L}$ is free on a generator $e$
([def-sc-invertible-module]) write $s|_V=a\cdot e$ with $a\in A$; then
$s(y)\neq0$ if and only if $a\notin\mathfrak p_y$, so $W\cap V=D(a)$. By
hypothesis $W\neq\emptyset$, so its complement is a closed subset not
containing all of $X_K$; by (1) it misses some $x_K$, i.e. $x_K\in W$.

(3) A smooth projective curve is in particular a curve over $k$
([def-pc-smooth-projective-curve]), hence an integral scheme of
dimension one ([def-pc-curve]); in particular $X\neq\emptyset$ and its
generic point $\eta$ is not closed. Every $x\in X(k)$ is a closed point
(its residue field is $k$). If $X(k)$ were finite, it would be a finite
union of closed points, hence a closed subset of $X$ not containing
$\eta$; but $X(k)$ is dense in $X$ by [lem-pc-rational-points-dense], so
its closure is $X\ni\eta$, a contradiction. Hence $X(k)$ is infinite.
For the last assertion let $0\neq s\in H^0(X,\mathcal{L})$. Since $X$ is
integral, restriction of sections of $\mathcal{L}$ to the generic point is
injective on every nonempty open (on an affine open
$\operatorname{Spec}A$ trivialising $\mathcal{L}$, with $A$ a domain, $s=a\cdot e$ and
$a\neq0$ in $A\subseteq\operatorname{Frac}A=\kappa(\eta)$), so $s_\eta\neq0$ in the
one-dimensional $\kappa(\eta)$-vector space $\mathcal{L}_\eta=\mathcal{L}(\eta)$; thus $s$ does not
vanish at $\eta$ and (2) (with $K=k$) gives $x\in X(k)$ with $s(x)\neq0$.

*Remark on base change.* For a general extension $K/k$ the hypothesis
of (2) holds for every non-zero $s$ as soon as $X_K$ is integral (by the
generic-point argument of (3) applied on $X_K$); for a smooth projective
curve with a rational point this integrality is established later in
the twist-lemma block, where this statement is used in exactly that
form.
