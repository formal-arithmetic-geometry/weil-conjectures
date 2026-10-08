+++
id = "thm-nagata-blowup-flat-base-change"
kind = "theorem"
title = "Flat base change of blow-ups"
order = 117
uses = ["def-nagata-blowup-flat-base-change-map", "lemma-nagata-flat-pullback-rees", "lemma-nagata-global-blowup-overlap-cocycle", "prop-nagata-relative-proj-functoriality"]
+++
**Status.** Bypassed by the formalized route: blow-ups are never
base-changed along a flat morphism. Every base-change step the route takes
goes through the universal property
`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup` and
the chart pullback squares
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowup$\iota$`
instead.

The constructed comparison $\operatorname{bc}_g$ is an isomorphism over
$Y$.

## Proof

Relative Proj sends the graded equivalence of
[lemma-nagata-flat-pullback-rees] to an affine-local isomorphism.
Compatibility with degree zero identifies the structure maps, and the
localization cocycle glues the local isomorphisms.
