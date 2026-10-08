+++
id = "prop-trf-karoubi-independence"
kind = "theorem"
title = "Representative independence of the summand trace"
order = 2398
tags = ["latex:proposition"]
uses = ["def-trf-categorical-trace", "def-trf-karoubi-trace", "def-weil-finite-field-fiber", "def-weil-pbc-qbar-category", "prop-trf-trace-formal-laws", "thm-trf-trace-formula-e"]
+++
Fix the global finite-field datum
and the joint conventions of [def-trf-karoubi-trace]. Let
$(E,K)$ and $(F,L)$ represent the same object of
$D^b_c(X,\Qlb)$ with $K\in D^b_c(X,E)$, $L\in D^b_c(X,F)$. After
passage to a common finite overfield $M$ of $E$ and $F$, the two
transported objects become isomorphic, and the
summand traces of compatible
endomorphisms agree; the same holds for the competing Frobenius
endomorphisms and their iterates, and the comparisons are transitive.
Consequently the trace formula of [thm-trf-trace-formula-e] is
independent of the finite field of definition and of the
representative.

## Proof

The equality of the two representatives in the common-stage category
[def-weil-pbc-qbar-category] gives, after scalar extension to a
common field, an isomorphism of the transported perfect complexes under
which compatible idempotents and endomorphisms are transported; by the
conjugacy invariance and scalar-extension law of the categorical trace
[prop-trf-trace-formal-laws], the summand traces
[def-trf-karoubi-trace] agree and depend only
on the isomorphism class of the summand. Naturality in the
endomorphism and transitivity of the comparison follow from these two
laws of [prop-trf-trace-formal-laws], applied to the transporting
isomorphism; the Frobenius endomorphisms are transported by this
isomorphism, by the definition of the objects and morphisms of the
common-stage category of [def-weil-pbc-qbar-category].
