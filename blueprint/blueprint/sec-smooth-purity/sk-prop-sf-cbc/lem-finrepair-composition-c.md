+++
id = "lem-finrepair-composition-c"
kind = "lemma"
title = "Composition for constructibility alone"
order = 1599
uses = ["def-finrepair-property-c", "lem-weil-pbc-grothendieck-spectral-sequence", "thm-constructible-serre"]
+++
If $\mathcal C(f)$ and $\mathcal C(g)$ hold for composable
morphisms, then $\mathcal C(gf)$ holds, for the predicate of
[def-finrepair-property-c].

## Proof

For a constructible $F$, the terms
$E_2^{a,b}=R^ag_*R^bf_*F$ are constructible by the two hypotheses
of [def-finrepair-property-c].
The composition spectral sequence of
[lem-weil-pbc-grothendieck-spectral-sequence] converges to
$R^{a+b}(gf)_*F$.
For a fixed total degree the first-quadrant sequence stabilizes and
has a finite filtration on its abutment.
Each page uses kernels and cokernels between constructible sheaves,
and that finite filtration uses extensions. Thus
[thm-constructible-serre] proves the assertion.
