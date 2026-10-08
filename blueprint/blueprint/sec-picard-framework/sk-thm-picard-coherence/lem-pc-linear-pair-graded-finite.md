+++
id = "lem-pc-linear-pair-graded-finite"
kind = "lemma"
title = "A degree bound for a pair of linear forms"
order = 652
uses = ["def-pc-proj", "def-pc-standard-graded-algebra"]
+++
Let $S$ be a standard graded
$k$-algebra, and let $l_0,l_1\in S_1$ have no common zero on
$\operatorname{Proj}(S)$. There is an integer $N\ge1$ such that

$$
S_n=l_0S_{n-1}+l_1S_{n-1}\qquad(n\ge N).
$$

## Proof

Put $J=(l_0,l_1)$, a homogeneous ideal of $S$.
Choose degree-one generators $x_0,\ldots,x_m$ of $S$ as in
[def-pc-standard-graded-algebra]. For each $x_i$, the quotient
chart $\operatorname{Spec}((S/J)_{(x_i)})$ is the closed subscheme
of $D_+(x_i)$ cut out by $l_0/x_i$ and $l_1/x_i$.
Its underlying space is empty, by the hypothesis and
[def-pc-proj]. Its coordinate ring is consequently the zero
ring. Thus $1=0$ also in the localization $(S/J)[x_i^{-1}]$,
whose degree-zero subring it is. The defining equivalence relation
for localization now gives $x_i^{a_i}\in J$ for some $a_i\ge1$.

Choose $N=1+\sum_{i=0}^m(a_i-1)$. Every monomial of degree
$n\ge N$ in the $x_i$ contains a factor $x_i^{a_i}$, so belongs
to $J$. Such monomials span $S_n$, proving $S_n\subseteq J$.
Taking degree $n$ components of $J=(l_0,l_1)$ gives
$S_n=l_0S_{n-1}+l_1S_{n-1}$, as required.
