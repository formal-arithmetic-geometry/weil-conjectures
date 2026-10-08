+++
id = "lemma-nagata-strict-transform-chart-cocycle"
kind = "lemma"
title = "Cocycle for strict-transform charts"
order = 155
uses = ["def-nagata-strict-transform-chart-comparison-localized", "lemma-nagata-affine-blowup-restrict-cocycle", "lemma-nagata-strict-transform-chart-localization", "lemma-nagata-strict-transform-chart-localization-data"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

The localized strict-transform chart comparisons agree on double
localizations and satisfy the cocycle equality on triple chart overlaps.

## Proof

On an intersection of the $a$- and $a'$-charts, choose a basic affine
refinement on which both chart restrictions are defined. The ordinary
blow-up transition is the specified localization isomorphism; by
[lemma-nagata-affine-blowup-restrict-cocycle] its two composites on a
triple refinement agree. Localizing the quotient map
$C_a\twoheadrightarrow C_a^{\mathrm{st}}$ gives the quotient by the
localized power-torsion ideal, by
[lemma-nagata-strict-transform-chart-localization-data]. Thus the
ordinary transition descends uniquely to a transition of strict-transform
chart rings. The descended maps agree with the comparisons constructed
after localization by
[lemma-nagata-strict-transform-chart-localization]. On a triple
refinement their two composites become the same ordinary transition before
quotienting, hence are equal after quotienting. This proves both the
double-overlap compatibility and the cocycle.
