+++
id = "pqf-lem-finite-fp-locnoeth"
kind = "lemma"
title = "Finite over a locally Noetherian base is finitely presented"
order = 198
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-locnoeth", "pqf-lem-affine-open-locnoeth"]
+++
Let $S$ be a locally Noetherian scheme and
let $p:T\to S$ be a
finite morphism. Then $p$
is of finite presentation.

## Proof

Let $\operatorname{Spec}A\subset S$ be an affine open; $S$ is
locally Noetherian in the sense of [pqf-def-locnoeth]. By
[pqf-lem-affine-open-locnoeth] the ring $A$ is Noetherian, and by
the definition of finiteness in
[def-weil-pbc-scheme-conventions] the preimage
$p^{-1}(\operatorname{Spec}A)=\operatorname{Spec}B$ is affine with
$B$ a finite $A$-module, in particular a finitely generated
$A$-algebra. A finitely generated module over a Noetherian ring is
finitely presented: choosing a surjection $A^n\to B$, its kernel is a
submodule of the Noetherian module $A^n$, hence is finitely generated,
and a finitely generated module with a finite free presentation of
finite rank is finitely presented. So $B$ is a finitely presented
$A$-algebra. Hence every affine open of $S$ is covered by the
single affine open $p^{-1}(\operatorname{Spec}A)$ of $T$ whose
coordinate ring is finitely presented over the coordinate ring of that
affine open of $S$, and $p$ is quasi-compact because it is affine;
by [def-weil-pbc-scheme-conventions] the morphism $p$ is of
finite presentation.
