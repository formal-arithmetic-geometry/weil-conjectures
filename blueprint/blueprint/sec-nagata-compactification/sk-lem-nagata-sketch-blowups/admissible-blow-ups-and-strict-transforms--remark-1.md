+++
id = "admissible-blow-ups-and-strict-transforms--remark-1"
kind = "remark"
title = "Formalization route"
order = 137
+++
The formal development (`AlgebraicGeometry.StrictTransform`,
specialized to blow-ups as
`Scheme.IdealSheafData.strictTransform`) works with this
scheme-theoretic-closure definition directly, and proves the identification
over the preserved open ([lemma-nagata-strict-transform-over-complement])
by scheme-image flat base change for a quasi-compact flat monomorphism
(`Nagata.ker_comap_self`), not through the torsion-quotient chart
model. The chart-by-chart infrastructure below
([def-nagata-strict-transform-chart-ring] through
[prop-nagata-strict-transform-closed-fiber-product]) is accordingly
not formalized — with the exception of the chart surjectivity
([lemma-nagata-strict-chart-map-surjective]), which is proved in the
subring-generation form used by the formalized Tag 080E route; of the
power-torsion material only the affine algebraic layer
(`Submodule.powTorsion` and its localization/exactness lemmas) is.
The identification of the strict transform with the blow-up of the
extended ideal ([thm-nagata-strict-transform-is-blowup],
Stacks Tag 080E) *is* formalized, but by the universal-property route
recorded in [def-nagata-strict-transform-blowup-comparison] and the
revised proof of [thm-nagata-strict-transform-is-blowup] — a
comparison morphism into the fibre product which is a closed immersion by
a chart-wise surjectivity computation, together with schematic density of
the exceptional complement — rather than by gluing the chart-ring
isomorphisms.
