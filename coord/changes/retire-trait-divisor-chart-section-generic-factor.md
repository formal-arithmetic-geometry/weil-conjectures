# AlgebraicGeometry.Scheme.GaloisCover.trait_divisor_chart_section_generic_factor

## Reason

The assignment is listed as `retire` in `coord/retire-items.tsv`. The Sheaf module is a
proved duplicate of the adopted upstream module
`WeilConjectures.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor`.
The upstream declaration has a stronger interface with fewer hypotheses and is already
proved. The Sheaf duplicate is withdrawn, and its consumer is migrated in this delivery.
No target statement or source-library declaration is changed.

## Old

The module `lean/Sheaf/AlgebraicGeometry/Morphisms/TraitDivisorChartSectionGenericFactor.lean`
provided the declaration
`AlgebraicGeometry.Scheme.GaloisCover.trait_divisor_chart_section_generic_factor` with the
same name and a longer signature. Its private proof imports were
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitSectionLift`,
`WeilConjectures.AlgebraicGeometry.Morphisms.RootProductChartBaseChangeFactor`, and the
Sheaf duplicate of the generic normalization comparison.

## New

The Sheaf module is withdrawn through `deleted.txt`. The DAG attachment now points to the
existing upstream declaration in
`lean/WeilConjectures/AlgebraicGeometry/Morphisms/TraitDivisorChartSectionGenericFactor.lean`.
The direct consumer
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart` imports
the upstream trait-divisor module and calls the upstream theorem. It uses the upstream
`ε : S.functionField →+* FractionRing A` to construct the old witness
`Spec.map (CommRingCat.ofHom ε)` and packages the same conclusion.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart` | unclaimed | Replace the withdrawn Sheaf import and adapt the theorem application to the upstream signature. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor` | unclaimed | Indirect consumer; no source change required. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData` | unclaimed | Indirect consumer; no source change required. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal` | unclaimed | Indirect consumer; no source change required. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation` | unclaimed | Indirect consumer; no source change required. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource` | unclaimed | Indirect consumer; no source change required. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified` | unclaimed | Indirect consumer; no source change required. |

## Status

landed 20261020T235545-L-1189050 2026-10-20 (merge of deliver/B7/Sheaf.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor)
