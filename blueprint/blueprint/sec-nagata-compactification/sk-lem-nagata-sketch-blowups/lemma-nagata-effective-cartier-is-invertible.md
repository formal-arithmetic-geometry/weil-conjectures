+++
id = "lemma-nagata-effective-cartier-is-invertible"
kind = "lemma"
title = "An effective Cartier ideal is invertible"
order = 98
lean = ["AlgebraicGeometry.isEffectiveCartierCenter_iff_isInvertible_ker"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-invertible-ideal", "def-nagata-scheme-image-comparison", "lemma-nagata-scheme-image-universal", "lemma-nagata-scheme-theoretic-closure-minimal"]
+++
Every effective Cartier ideal is invertible as an ideal sheaf.

## Proof

The regular local generator gives an isomorphism from the structure sheaf
to the ideal on each member of the defining cover. On overlaps the two
generators differ by a unit, so these local rank-one bases glue.
