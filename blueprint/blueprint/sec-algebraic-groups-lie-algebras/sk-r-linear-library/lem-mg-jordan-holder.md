+++
id = "lem-mg-jordan-holder"
kind = "lemma"
title = "Elementary Jordan–Holder lemma"
order = 2542
uses = ["def-mg-weil-composition-series", "lem-mg-composition-series-exists"]
+++
Any two composition series of a finite-dimensional Weil representation
have the same simple factors, up to permutation and isomorphism and with
the same multiplicities.

## Proof

Use the terminology of [def-mg-weil-composition-series] and induct
on $\dim V$. Let $S\subseteq V$ be the first nonzero term of one
composition series, so
$S$ is simple. In a second composition
series

$$
0=V'_0\subsetneq V'_1\subsetneq\cdots\subsetneq V'_u=V,
$$

let $j$ be the least index for which $S\subseteq V'_j$. Then
$S\cap V'_{j-1}=0$, while the nonzero map
$S\to V'_j/V'_{j-1}$ is an isomorphism because both source and target
are simple. In particular

$$
V'_j=V'_{j-1}+S,
\qquad V'_j/V'_{j-1}\simeq S.
$$

Now pass the second series to $V/S$ by replacing every term by
$(V'_i+S)/S$. Consecutive terms at indices $j-1,j$ coincide and are
deleted. Before that repetition, the quotient factors are unchanged
because $S\cap V'_i=0$; after it, they are unchanged because
$S\subseteq V'_i$. Thus this is a composition series of $V/S$ whose
factors are exactly those of the second series with the single factor
isomorphic to $S$ removed. The first series, after its first term, also
induces a composition series of $V/S$. The induction hypothesis matches
their remaining factors, and adjoining $S$ proves the assertion.
Existence of the series used here is supplied by
[lem-mg-composition-series-exists].
