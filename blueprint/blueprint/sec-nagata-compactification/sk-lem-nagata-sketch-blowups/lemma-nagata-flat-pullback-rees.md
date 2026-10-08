+++
id = "lemma-nagata-flat-pullback-rees"
kind = "lemma"
title = "Flat pullback of the Rees algebra"
order = 115
uses = ["def-nagata-flat-pullback-rees-map", "lemma-nagata-flat-pullback-ideal-pow"]
+++
**Status.** Bypassed by the formalized route: blow-ups are never
base-changed along a flat morphism. Every base-change step the route takes
goes through the universal property
`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup` and
the chart pullback squares
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowup$\iota$`
instead.

The map $\beta_g$ is a graded algebra equivalence.

## Proof

Apply [lemma-nagata-flat-pullback-ideal-pow] in every degree and check
compatibility with multiplication. The degreewise isomorphisms assemble
to the claimed graded equivalence.
