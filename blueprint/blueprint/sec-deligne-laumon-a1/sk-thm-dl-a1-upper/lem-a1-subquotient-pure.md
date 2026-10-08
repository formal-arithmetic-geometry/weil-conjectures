+++
id = "lem-a1-subquotient-pure"
kind = "lemma"
title = "Irreducible lisse subquotients of a pure lisse sheaf are pure of the same weight"
order = 2791
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "def-wf-weil-category", "lem-a1-spectrum-exact-sequence"]
+++
Let $X_0$ be a separated
finite-type $k_0$-scheme and let $\mathcal G$ be a lisse
Weil sheaf on $X_0$ (lisse in the sense
of [def-weil-pbc-constructible-complexes]) which is punctually
$\iota$-pure of weight $w\in\mathbf R$ in the sense of
[def-weil-punctual-weights]. Then every irreducible lisse subquotient
$\mathcal S$ of $\mathcal G$ is punctually $\iota$-pure of weight
$w$.

## Proof

Fix a closed point $x$ and let $(V_x,F_x)$ be the stalk Frobenius
module of $\mathcal G$ at $x$, with eigenvalue multiset $S_x$ as in
[def-weil-punctual-weights]. The geometric stalk functor of the
constructible conventions of [def-weil-pbc-constructible-complexes]
is exact, so the stalk module of $\mathcal S$ at $x$ is an
$F_x$-stable subquotient of $(V_x,F_x)$; hence its eigenvalue multiset
is a submultiset of $S_x$, which is the spectrum bookkeeping of
[lem-a1-spectrum-exact-sequence] applied successively to the
subobject and to the quotient. Every eigenvalue of $(V_x,F_x)$ has
$\iota$-modulus $q_x^{w/2}$ by the punctual purity of weight $w$ of
[def-weil-punctual-weights], hence so does every eigenvalue of the
stalk module of $\mathcal S$; the closed point $x$ was arbitrary, so
$\mathcal S$ is punctually $\iota$-pure of weight $w$.
