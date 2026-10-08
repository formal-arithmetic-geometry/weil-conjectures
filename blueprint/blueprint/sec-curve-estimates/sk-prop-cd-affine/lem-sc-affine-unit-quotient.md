+++
id = "lem-sc-affine-unit-quotient"
kind = "lemma"
title = "Units modulo powers on an affine curve"
order = 1020
uses = ["def-sc-curves", "lem-sc-compactification", "lem-sc-divisor-class-curve", "lem-sc-global-functions"]
+++
Let $C$ be a smooth affine connected curve
over an algebraically closed field $k$, and let $n\geq1$.
Then $\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}$
is finite.

## Proof

Choose $C\subseteq\overline C$ with finite complement $S$
by [lem-sc-compactification]. The divisor of a unit is
supported on $S$. Its divisor is zero if and only if it and its
inverse extend regularly to $\overline C$: this is the valuation
criterion in [lem-sc-divisor-class-curve]. Such an extended
unit belongs to $k^\times$ by [lem-sc-global-functions].
Consequently the divisor map identifies
$\mathcal O_C(C)^\times/k^\times$ with a subgroup $L$ of
$\bigoplus_{P\in S}\mathbf Z[P]$. A subgroup of a finite rank
free abelian group is finitely generated free, so $L/nL$ is finite.
The natural map from the unit group modulo powers to $L/nL$ is
surjective. It is injective: if $\operatorname{div}(u)=n\operatorname{div}(v)$
for a unit $v$, then $u/v^n\in k^\times$, which has an $n$-th
root because $k$ is algebraically closed. Thus $u$ is an
$n$-th power, and the desired quotient is isomorphic to $L/nL$.
