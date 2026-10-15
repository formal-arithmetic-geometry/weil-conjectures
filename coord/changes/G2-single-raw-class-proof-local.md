# G2: proof-local continuity reduction

## Reason

The item needs a filtered-colimit injectivity argument after descent of a raw
class. The preflight flags the section-local attribute command as a possible
change to what importers see, so this record documents its scope.

## Old

`Sheaf.AlgebraicGeometry.CartesianHigherImageSingleRawClassVanishing` (held by G2)
had its original public statement imports and one unproved theorem,
`exists_cartesianHigherImage_single_raw_class_eq_zero`.

## New

The existing theorem has the same signature and a complete proof from a new
chart-representative theorem and existing continuity declarations. The item adds
the proved private lemmas `iso_reflects_zero` and `restrictedOver_eventually_zero`,
four private proof imports, and a section-local `irreducible` attribute on
`restrictedOverCohomology` and `restrictedOverCohomologyMap`. That attribute ends
at the section's `end` and changes elaboration of the private proof only.

The new module `Sheaf.AlgebraicGeometry.CartesianRawClassChartRepresentative`
contains the public theorem `exists_cartesianRawClass_chart_representative`, with
its own node, source and full proof in words. Its sole sorry separates descent
and map compatibility from the proved continuity injectivity argument.

## Users

No existing public signature, definition, visibility or public import changes.
No other existing module is adapted, and no target's meaning changes. Existing
importers see the same original theorem. The new theorem is a private proof
dependency of the item. The report counts this as a decomposition with zero net
reduction of holes.

## Status

landed 20261015T041333-L-536434 2026-10-15 (merge of deliver/G2/Sheaf.AlgebraicGeometry.CartesianHigherImageSingleRawClassVanishing)
in report.md. Both delivered modules compile through lcompile.py within the unchanged
60-second per-file limit. No existing signature or public import changes.
