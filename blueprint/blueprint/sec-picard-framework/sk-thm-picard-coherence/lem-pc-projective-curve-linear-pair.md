+++
id = "lem-pc-projective-curve-linear-pair"
kind = "lemma"
title = "Two linear forms without a common zero on a projective curve"
order = 648
uses = ["def-pc-curve", "def-pc-proj", "def-pc-standard-graded-algebra", "lem-pc-finite-linear-avoidance"]
+++
Let $k$ be an infinite field and $S$ an integral
standard graded $k$-algebra
such that $X=\operatorname{Proj}(S)$ is a
curve. There exist
$l_0,l_1\in S_1$ such that $D_+(l_0)\cup D_+(l_1)=X$.

## Proof

The vector space $S_1$ is nonzero, since otherwise $S=k$ and
$\operatorname{Proj}(S)$ is empty. Choose $0\ne l_0\in S_1$.
The homogeneous prime $(0)$ is the generic point of $X$, so it is
not in $V_+(l_0)$, by [def-pc-proj] and the integrality of $S$.
Thus $V_+(l_0)$ is a proper closed subset of the Noetherian integral
one-dimensional space $X$ of [def-pc-curve].
Such a closed subset is a finite set of closed points: it has
finitely many irreducible components by Noetherianity, and each
component has dimension zero, because adjoining $X$ to a chain of
proper irreducible closed subsets increases its length by one.
A zero-dimensional irreducible closed subset is its single generic
point, which is closed.

For each point $x$ in that finite set, its homogeneous prime
$\mathfrak p_x$ gives a proper subspace
$W_x=\mathfrak p_x\cap S_1$ of $S_1$. Indeed, containment of all
of $S_1$ would imply containment of $S_+$, since degree-one elements
generate $S$ by [def-pc-standard-graded-algebra]; that is
excluded for a point of Proj. The finite-dimensional space $S_1$
contains an $l_1$ outside the union of these subspaces by
[lem-pc-finite-linear-avoidance]. It does not vanish at any
point where $l_0$ vanishes, which proves the asserted cover.
