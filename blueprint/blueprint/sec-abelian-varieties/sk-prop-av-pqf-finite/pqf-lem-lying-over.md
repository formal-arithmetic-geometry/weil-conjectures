+++
id = "pqf-lem-lying-over"
kind = "lemma"
title = "Lying over for an injective integral extension"
order = 531
+++
Let $A\hookrightarrow B$ be an injective integral map of rings. Then
every prime $\mathfrak p\subset A$ is the contraction of a prime of
$B$.
(*Classical: this is the lying-over theorem; Stacks Project,
Algebra, Lemma 10.36.22, Tag
[00GU](https://stacks.math.columbia.edu/tag/00GU), is the going-up
companion of it, and its proof invokes lying over as Algebra Lemma
10.36.17.*)

## Proof

Put $S=A\setminus\mathfrak p$. Localization gives an injective integral
map $A_{\mathfrak p}\hookrightarrow S^{-1}B$; the target is nonzero
because the map is injective. Choose a maximal ideal $\mathfrak m$ of
$S^{-1}B$. Its contraction is maximal in $A_{\mathfrak p}$: after
quotienting, $S^{-1}B/\mathfrak m$ is a field integral over the
contracted domain, and a domain over which a field is integral is
itself a field (an integral equation for $a^{-1}$ expresses $a^{-1}$ in
the domain for each nonzero $a$). The only maximal ideal of
$A_{\mathfrak p}$ is $\mathfrak pA_{\mathfrak p}$. Pulling
$\mathfrak m$ back to $B$ therefore gives a prime whose contraction is
$\mathfrak p$.
