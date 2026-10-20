# AlgebraicGeometry.affine_pushforward_colimit

## Reason

Restore the module assigned in `coord/rework.tsv` from its preserved quarantine source.
After upstream sync 5f7b33eac, the statement's `Scheme.CommAlgebraSheaf` API is available
only through private proof imports. The archived file fails at line 70 with
`Invalid field CommAlgebraSheaf`; the compiler explicitly requests a public import of
`WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`.

Add that public statement dependency. The theorem text, proof body, definitions,
attributes, all other imports, and DAG attachment/dependencies are preserved verbatim.
This repairs elaboration; it does not claim to prove the existing theorem hole.
No target statement or definition changes meaning, so no semantic target review is reopened.

## Old

The file is absent from `lean/` and preserved at
`quarantine/Sheaf/AlgebraicGeometry/AffinePushforwardColimit.lean`.
Its public imports are:

```lean
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
```

## New

Restore the preserved module at `lean/Sheaf/AlgebraicGeometry/AffinePushforwardColimit.lean`,
adding exactly this line to its statement imports:

```lean
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
```

All subsequent source text is byte-for-byte unchanged.

## Users

The live-source scan finds no importers because this module and its consumer chain were
quarantined together. The direct preserved importer is
`Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent`; its original source is compiled
against this restoration during validation, without being adapted or included in delivery.
The table includes the item and all downstream rework rows whose recorded failure names
this missing module. Restoring the public API changes no consumer proposition.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffinePushforwardColimit | K3 | Restored with the explicit statement import; theorem unchanged. |
| Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Quarantined downstream module; signature and intended dependency unchanged; no adaptation. |

## Status

landed 20261020T150653-L-2565839 2026-10-20 (merge of deliver/K3/Sheaf.AlgebraicGeometry.AffinePushforwardColimit)
