+++
id = "lem-weil-pbc-finite-pullback-identities"
kind = "lemma"
title = "Finite-pullback identities"
order = 1079
uses = ["def-weil-pbc-finite-section-pullback", "def-weil-pbc-inverse-image"]
+++
Finite pullback of sections, in the sense of
[def-weil-pbc-finite-section-pullback], satisfies the following four
equations: identity pullback fixes a section; pullback along a composite
equals the composite pullback; pullback commutes with restriction to the
closed fiber; and a section descended from a finite surjective refinement
pulls back to the chosen local section on that refinement.

## Proof

The first three equations are the functoriality of the inverse-image unit of
[def-weil-pbc-inverse-image], applied to the identities $V\times_YY=V$, to
composites, and to the cartesian square defining the closed fiber of
[def-weil-pbc-finite-section-pullback]. The fourth is the uniqueness
statement in finite descent, applied to the local sections selected on the
refinement.
