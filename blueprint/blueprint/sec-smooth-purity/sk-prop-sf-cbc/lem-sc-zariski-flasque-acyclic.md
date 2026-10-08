+++
id = "lem-sc-zariski-flasque-acyclic"
kind = "lemma"
title = "Flasque sheaves are acyclic"
order = 1556
uses = ["def-sc-zariski-cohomology", "def-sc-zariski-flasque"]
+++
For a flasque abelian sheaf
$F$ on a topological space, $H^q(X_{\rm Zar},F)=0$ for
$q>0$, in the resolution sense of
[def-sc-zariski-cohomology].

## Proof

We use the elementary flasque-resolution lemma of sheaf
homological algebra: if $0\to F\to I\to Q\to0$ is exact
and $F$ is flasque, then $I(V)\to Q(V)$ is surjective
for every open $V$; if $I$ is flasque then $Q$ is
flasque. For the first assertion, choose local lifts of
a section of $Q$, and glue them by correcting their
differences, which lie in $F$, using the restriction
surjectivity in [def-sc-zariski-flasque].
One can perform the gluing by a well-ordering of a cover:
at a successor stage extend the difference from the
intersection using flasqueness; at a limit stage use
the sheaf axiom on the union.
For the second assertion, lift a section of $Q(U)$
to $I(U)$, extend it to $I(V)$, and project to $Q(V)$.
Injective sheaves are flasque: a section on an open $U$
is a morphism from the free abelian sheaf extended by zero
from $U$, whose inclusion into the corresponding sheaf
for $V$ is a monomorphism; injectivity extends the map.
Embed $F$ in an injective $I$, and iterate this argument
on the flasque quotient $Q$.
The resulting injective resolution stays exact on sections.
The definition in [def-sc-zariski-cohomology] gives the
claimed vanishing.
