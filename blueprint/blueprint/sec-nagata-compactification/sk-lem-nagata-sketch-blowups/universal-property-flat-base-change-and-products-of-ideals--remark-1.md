+++
id = "universal-property-flat-base-change-and-products-of-ideals--remark-1"
kind = "remark"
title = "Formalization route"
order = 111
+++
The formal proof (`exists_lift_blowup` together with
`hom_ext_of_isInvertible_comap`) takes the
Stacks-style hypothesis that the inverse image ideal sheaf of the center is
effective Cartier, and is entirely chart-local: existence is glued from the
universal property of the chart ring $A[\mathcal I/a]$
(`AffineBlowup.chartRingLift`) on affine probes, and uniqueness
follows from chart-ring extensionality
(`chartRingHom_ext`) together with the chart-overlap localization.
The graded-map and tensor-power scaffolding
([thm-nagata-blowup-universal-property],
[lemma-nagata-invertible-ideal-tensor-power],
[lemma-nagata-relative-proj-invertible-tensor-powers],
[thm-nagata-blowup-universal-property]) is not formalized.
