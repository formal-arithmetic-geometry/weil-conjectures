+++
id = "thm-exc-curve-open-constructible-general"
kind = "theorem"
title = "Open direct-image constructibility on arbitrary curves"
order = 1920
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-exc-dvr-galois", "lem-exc-field-discrete-modules", "lem-exc-punctured-curve-branches", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-exc-curve-open-dimension-general", "thm-fin-open-degree-zero"]
+++
Let $T$ be of finite type of dimension at most one over
a finite field or its algebraic closure, let
$j:U\hookrightarrow T$ be open, and let $A$ be finite
and killed by a power of a prime invertible on $T$.
For a constructible
etale $A$-module sheaf $F$, every
$R^qj_*F$ is
constructible on $T$.

## Proof

Degree zero is [thm-fin-open-degree-zero]; degrees
greater than one vanish by
[thm-exc-curve-open-dimension-general].
For degree one, the stalk calculation just used, namely
[prop-weil-pbc-strict-henselization-stalk-formula], [lem-exc-punctured-curve-branches],
reduces a stalk at a closed boundary point to the finite
product of the first cohomology groups of its branch fields.
The pullback of $F$ to each field has a finite geometric
fibre by [def-weil-pbc-constructible-complexes].
The equivalence in [lem-exc-field-discrete-modules]
therefore gives a finite Galois module. The finiteness
part of [lem-exc-dvr-galois] proves that each of these
degree-one stalks is finite.

The sheaf is zero on $U$, since $j^*j_*$ is the
identity, and on $T\setminus\overline U$, where the
inverse image of $U$ is empty, using
[def-weil-pbc-direct-image]. The boundary
$\overline U\setminus U$ is a finite set of closed
points: it is a closed subset of the Noetherian
one-dimensional $\overline U$ and contains none of its
generic points. At each of these closed point schemes,
a finite continuous Galois module is finite locally
constant by [lem-exc-field-discrete-modules].
These point strata together with the open complement
give the finite lisse partition required by
[def-weil-pbc-constructible-complexes].
