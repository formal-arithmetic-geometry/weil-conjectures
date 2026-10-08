+++
id = "sbc-lem-bc-minimal-counterexample"
kind = "lemma"
title = "Minimal counterexamples occur over a point"
order = 1386
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $T$ be a
quasi-compact and
quasi-separated scheme and let $P$ be a property for quasi-compact
quasi-separated schemes over $T$. Assume:

1. if $T''\to T'$ is a thickening of quasi-compact quasi-separated
schemes over $T$, then $P(T'')$ if and only if $P(T')$;
1. if $T'=\varprojlim T_i$ is a limit of an inverse system of
quasi-compact quasi-separated schemes over $T$ with affine
transition morphisms and $P(T_i)$ holds for all $i$, then
$P(T')$ holds;
1. if $Z\subset T'$ is a closed subscheme with quasi-compact
complement $V\subset T'$ and $P(T')$ holds, then either $P(V)$
or $P(Z)$ holds;
1. $P(\emptyset)$ does not hold.

Then $P(T)$ implies $P(\operatorname{Spec}K)$ for some morphism
$\operatorname{Spec}K\to T$ where $K$ is a field.
(*Stacks Project, Lemma 59.88.5, [Tag `0F06`](https://stacks.math.columbia.edu/tag/0F06).*)

## Proof

Consider the set $\mathfrak T$ of closed subschemes $T'\subset T$ such
that $P(T')$; ordered by inclusion ($T''\subset T'$ means the closed
immersion), a chain has a lower bound by (2) applied to the inverse
system of its members (their transition morphisms are closed
immersions, hence affine), so by Zorn's lemma $\mathfrak T$ has a
minimal element $T'$, and $T'\neq\emptyset$ by (4). If $T'$ is not reduced, then the reduction
$T'_{\mathrm{red}}\to T'$ is a thickening, and (1) gives
$P(T'_{\mathrm{red}})$, contradicting the minimality of $T'$ as
$T'_{\mathrm{red}}$ is a strictly smaller closed subscheme; hence $T'$
is reduced. Let $\eta\in T'$ be the generic point of an irreducible
component of $T'$; then $\eta=\operatorname{Spec}K$ for a field $K$
and $\eta=\varprojlim V$ over the affine open subschemes $V\subset T'$
containing $\eta$. For such a $V$, the complement $Z=T'\setminus V$ is
closed with quasi-compact complement $V$, and if $P(V)$ failed then by
(3) $P(Z)$ would hold, contradicting the minimality of $T'$ ($Z$ is
strictly smaller than $T'$ since $\eta\in V$); hence
$P(V)$ holds for all these $V$, and (2) applied to the limit gives
$P(\eta)=P(\operatorname{Spec}K)$.
