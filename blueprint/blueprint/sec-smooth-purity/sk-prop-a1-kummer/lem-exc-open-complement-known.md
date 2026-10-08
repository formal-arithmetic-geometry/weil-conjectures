+++
id = "lem-exc-open-complement-known"
kind = "lemma"
title = "The open-complement condition from the direct-image input"
order = 1923
uses = ["def-exc-open-complement-bound", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-exc-curve-open-constructible-general", "thm-exc-curve-open-dimension-general", "thm-exc-direct-image-input-holds"]
+++
Let $k$ be the algebraic closure of a finite field, let $T$ be a
finite-type $k$-scheme of dimension at most $d$, let
$j:V\hookrightarrow T$ be a
quasi-compact open immersion,
and let $A$ be a finite ring annihilated by a power of a prime
$\ell\neq\operatorname{char}(k)$. Then the pair $(V,T)$ satisfies the
open-complement condition of [def-exc-open-complement-bound] with
$c=2d$.
Independently of the general argument, the condition is immediate in
dimension zero, where an open immersion of a zero-dimensional Noetherian
scheme is also closed and both clauses are immediate, and it is proved in
dimension at most one in
[thm-exc-curve-open-dimension-general], [thm-exc-curve-open-constructible-general].

## Proof

The field $k$ is separably closed, so both clauses of the direct-image
finiteness input hold over $k$ by
[thm-exc-direct-image-input-holds]. The constructibility clause is
its clause (1) applied to the open immersion $j$,
which is of finite type because it is quasi-compact and $T$ is of finite
type over $k$.
For the vanishing clause, fix a geometric point $\bar t$ of $T$. The
strict-henselization stalk formula
[prop-weil-pbc-strict-henselization-stalk-formula] identifies the
stalk of the higher direct image with the cohomology of the open
complement over the strict henselization at $\bar t$,

$$
\bigl(R^qj_*M\bigr)_{\bar t}
\;\cong\;H^q\bigl(V\times_TT_{(\bar t)},M\bigr),
$$

a filtered colimit of the groups $H^q(V\times_TU,M)$ over the pointed
etale neighbourhoods $U\to T$ of $\bar t$; each $V\times_TU$ is an
open subscheme of the etale $T$-scheme $U$, hence a finite-type
$k$-scheme of dimension at most $d$. As $k$ is separably closed,
clause (2) of that input gives
$H^q(V\times_TU,M)=0$ for $q>2d$ and every torsion sheaf $M$, and
vanishing is preserved by the filtered colimit. Hence every geometric
stalk of $R^qj_*M$ vanishes for $q>2d$, and conservativity of
geometric stalks ([lemma-weil-pbc-geometric-stalk-conservative]) makes
the sheaf itself zero, which is the vanishing clause with $c=2d$.
