+++
id = "lem-fet-finite-limits"
kind = "theorem"
title = "Finite limits and colimits of finite etale covers"
order = 974
uses = ["def-galois-categories", "def-weil-pbc-scheme-conventions", "lem-fet-locally-trivial"]
+++
Let $Y$ be a scheme. Then $\mathrm{F\acute Et}(Y)$ has finite limits and
finite colimits, and for every morphism $Y'\to Y$ the base change functor
is exact.

## Proof

Step 1: finite limits. With $\mathrm{F\acute Et}(Y)$ as in
[def-galois-categories] and the scheme-theoretic fibre products of
[def-weil-pbc-scheme-conventions], the final object is $Y$, and fibre products of
finite etale $Y$-schemes are finite etale over $Y$; base change
commutes with these operations, so it is left exact.
Step 2: finite colimits. Finite coproducts are disjoint unions and the
initial object is the empty scheme, so it remains to construct coequalizers
of a pair $a,b:Z\to Y$ in $\mathrm{F\acute Et}(Y)$. By
[lem-fet-locally-trivial] applied over the members of an etale cover,
and because the existence of a coequalizer which is finite etale is a
statement local on the target for the etale topology, we may assume
$Y=\coprod_{i=1}^nY$ and $Z=\coprod_{j=1}^mY$; the two morphisms then
correspond to maps of index sets
$a_s,b_s:\{1,\dots,m\}\to\{1,\dots,n\}$, after a further Zariski
refinement. Let $T$ be the coequalizer of $a_s,b_s$ in finite sets.
Then $\coprod_{t\in T}Y$, with the evident structure morphisms, is a
coequalizer of $a,b$ in $\mathrm{F\acute Et}(Y)$: an object
$W\to Y$ of $\mathrm{F\acute Et}(Y)$ is, etale-locally, of the form
$\coprod_{i\in I}Y$, and morphisms to it are maps of index sets, so the
universal property reduces to the universal property of $T$. It is
finite etale over $Y$, and base change commutes with the construction, so
base change is right exact.
