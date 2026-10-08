+++
id = "lem-sc-normal-dim1-dvr"
kind = "lemma"
title = "One-dimensional normal local rings"
order = 917
+++
A one-dimensional noetherian normal local domain is a discrete
valuation ring.

## Proof

This is the classical equivalence: for a noetherian local domain
$(R,\mathfrak m)$ of dimension one, $R$ is a DVR if and only
if $R$ is integrally closed if and only if $\mathfrak m$ is
principal (*reference: Stacks Project, Commutative Algebra,
[Tag 00PD](https://stacks.math.columbia.edu/tag/00PD): for a noetherian local domain of dimension one, being a
discrete valuation ring is equivalent to being integrally closed;
the nontrivial implication, integrally closed $\Rightarrow$
principal, is proven in loc. cit. as follows: choose
$0\neq a\in\mathfrak m$; $R/(a)$ is Artinian, so
$\mathfrak m^n\subseteq(a)$ for some $n$, and choosing $n$
minimal there is $b\in\mathfrak m^{n-1}\setminus(a)$; then
$x:=a/b\notin R$, so $x$ is not integral over $R$, hence
$x\mathfrak m\nsubseteq\mathfrak m$ by the integrality
criterion, while $x\mathfrak m\subseteq R$; an element
$y\in\mathfrak m$ with $xy\in R\setminus\mathfrak m$ is then a
generator of $\mathfrak m$)*.
