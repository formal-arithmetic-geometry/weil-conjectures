+++
id = "lemma-nagata-affine-blowup-restrict-cocycle"
kind = "lemma"
title = "Identity and cocycle laws for affine restriction"
order = 47
lean = ["AlgebraicGeometry.AffineBlowup.hom_comp"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-localization-mul", "lemma-nagata-rees-localization-one", "lemma-nagata-rees-piece-membership", "prop-nagata-affine-blowup-restrict", "prop-nagata-rees-graded"]
+++
The restriction isomorphism is the identity for $s=1$, and its two possible
composites on an iterated basic open $D(st)$ agree literally after the
chosen canonical associativity isomorphisms.

## Proof

On each standard chart, the map for $s=1$ is induced by the identity of the
Rees algebra, hence is the identity. For $s,t$, both composites send a
homogeneous fraction to its image in the localization at $st$; the two
coefficient maps are equal by [lemma-nagata-rees-localization-one]
and [lemma-nagata-rees-localization-mul].
The chart maps therefore agree on a cover, proving the asserted identity
and cocycle equalities globally.
