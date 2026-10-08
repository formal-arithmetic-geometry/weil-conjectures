+++
id = "lem-sc-generic-cohomology-comparison"
kind = "lemma"
title = "Generic replacement in degrees at least two"
order = 1005
uses = ["def-sc-curves", "def-sc-function-field", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-sheaves", "lem-sc-zero-generic-acyclic", "prop-weil-pbc-strict-henselization-stalk-formula"]
+++
Let $C/k$ be a smooth integral separated
curve over algebraically closed $k$,
and let $\eta:\operatorname{Spec}k(C)\to C$ be its generic point,
with function field $k(C)$.
For every torsion etale sheaf
$F$, the adjunction map induces

$$
H^q(C,F)\ \xrightarrow{\ \sim\ }\ H^q(C,\eta_*\eta^*F)
\qquad(q\geq2)
$$

on cohomology.

## Proof

The generic restriction of $\eta_*M$ is $M$: after a geometric
generic base change the source is the same separably closed
point, as is also seen in
[prop-weil-pbc-strict-henselization-stalk-formula] in degree zero.
Hence the kernel and cokernel of $F\to\eta_*\eta^*F$ both
have zero generic restriction. They are acyclic by
[lem-sc-zero-generic-acyclic]. Write the map as a
surjection onto its image followed by an injection. The two
long exact sequences give the displayed isomorphism for $q\geq2$.
