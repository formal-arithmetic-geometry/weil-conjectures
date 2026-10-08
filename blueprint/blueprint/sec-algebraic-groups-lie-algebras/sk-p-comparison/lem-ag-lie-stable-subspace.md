+++
id = "lem-ag-lie-stable-subspace"
kind = "lemma"
title = "Group-invariant and Lie-invariant subspaces agree"
order = 2497
uses = ["def-wf-algebraic-components", "def-wf-algebraic-representations", "def-wf-lie-algebra-derivation", "lem-ag-cartier-reduced", "lem-wf-same-lie-closed-subgroup"]
+++
Let $H\subseteq\operatorname{GL}(V)$ be a connected closed matrix group
over $k=\overline{\mathbf Q}_\ell$ (connected in the sense of
[def-wf-algebraic-components]), with Lie algebra
$\mathfrak h=\operatorname{Lie}(H)$ as in
[def-wf-lie-algebra-derivation], and let $r:H\to\operatorname{GL}(M)$ be
a rational representation, i.e. an algebraic-group module in the sense
of [def-wf-algebraic-representations]. Its differential
$dr:\mathfrak h\to\operatorname{End}(M)$ is defined by

$$
r(1+\varepsilon X)=1+\varepsilon\,dr(X)
\qquad\text{in }\operatorname{GL}(M)(k[\varepsilon]/\varepsilon^2),
\quad X\in\mathfrak h .
$$

Then a subspace $U\subseteq M$ is $H$-invariant if and only if
$dr(X)U\subseteq U$ for every $X\in\mathfrak h$.

## Proof

The entries of $r$ are regular functions on $H$, i.e. restrictions of
polynomials in the matrix entries and $\det^{-1}$; so $r$ may be
evaluated on $R$-points of $H$ for every commutative $k$-algebra $R$.
Since $r(1)=1$, the value $r(1+\varepsilon X)$ has the form
$1+\varepsilon Y$, so $dr$ is well defined and linear. The identities
$r(gh)=r(g)r(h)$ and $r(g^{-1})=r(g)^{-1}$ hold on $k$-points, hence
as identities of regular functions on the reduced varieties $H\times H$
and $H$; consequently they hold on $R$-points.

Choose a basis of $M$ whose first $u=\dim U$ vectors span $U$, and write
$r(g)$ in block form $\begin{pmatrix}a(g)&b(g)\\c(g)&d(g)\end{pmatrix}$,
with $c(g)$ the lower-left $(\dim M-u)\times u$ block. Let
$\mathcal S\subseteq\operatorname{GL}(V)$ be the closed subscheme cut
out by the ideal of $H$ together with the entries of $c$. Its $R$-points
are the $g\in H(R)$ such that $r(g)$ is block upper triangular. Block
upper triangular invertible matrices are closed under products and
inverses, and $r$ is multiplicative on $R$-points, so multiplication and
inversion of $\operatorname{GL}(V)$ restrict to $\mathcal S$. By
[lem-ag-cartier-reduced], $\mathcal S$ is reduced; it is the closed
subgroup

$$
S=\{g\in H:r(g)U\subseteq U\},
$$

and its Lie algebra is computed by the defining equations: $X\in
\operatorname{Lie}(S)$ exactly when $1+\varepsilon X$ is a
$k[\varepsilon]/\varepsilon^2$-point of $H$, i.e. $X\in\mathfrak h$
(again by [lem-ag-cartier-reduced] applied to $H$), and the lower-left
block of $r(1+\varepsilon X)=1+\varepsilon\,dr(X)$ vanishes. Thus

$$
\operatorname{Lie}(S)=\{X\in\mathfrak h:dr(X)U\subseteq U\}.
$$

If $U$ is $H$-invariant, then $S=H$, so
$\operatorname{Lie}(S)=\mathfrak h$ and every $dr(X)$ preserves $U$.
Conversely, if every $dr(X)$ preserves $U$, then
$\operatorname{Lie}(S)=\mathfrak h=\operatorname{Lie}(H)$. Since $H$ is
connected and $S\subseteq H$ is a closed algebraic subgroup,
[lem-wf-same-lie-closed-subgroup] gives $S=H$, i.e. $U$ is
$H$-invariant.
