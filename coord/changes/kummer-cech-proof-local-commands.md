# AlgebraicGeometry.ProEtale.CondensedRing.cechImage_additive

## Reason

The proof-only local commands keep the concrete inverse/direct image functors from
unfolding during elaboration of the two completed categorical proofs. The linter
setting suppresses an unused section-variable warning on the existing
`cosimplicialGrothendieck` theorem. These commands do not change exported attributes,
public signatures, definition bodies, public imports or target meanings. Preflight
classifies their textual addition as requiring this record.

## Old

No local reducibility commands before the namespace. The theorem
`cosimplicialGrothendieck` had no locally scoped linter option. All its binders,
its type and its instance registration are retained verbatim.

## New

```lean
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
```

Immediately before the existing docstring and declaration of
`cosimplicialGrothendieck`:

```lean
set_option linter.unusedSectionVars false in
```

Two added imports are private proof imports. The original public imports and both
existing instance registrations remain verbatim. No consumer needs adaptation.

## Users

`tools/downstream.py Sheaf.Paper.KummerCechDescent` lists these consumers.
Its `--uses cechImage_additive` and `--uses cosimplicialGrothendieck` searches find
only this module's declaration and instance-registration lines. The direct
importers are `KummerNormalizedComparison` and `KummerNerveCoordinates`.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.KummerBarResolution` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerChartGeometryMaps` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerCoefficientModels` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerCoherentRoof` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerConstantNerveTerm` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerGeometricColumns` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerGlobalChart` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerInvariantScalarMap` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerLocalSource` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerNerveCoordinates` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerNerveGeometricMap` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerNerveTransport` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerNormalizedChart` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerNormalizedComparison` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerParameterizedTerm` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveChart` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveCoordinates` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveMorphism` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveNaturality` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveScalarMorphism` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerRefinement` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerResolutionColumns` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerResolvedDescent` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerScalarInvariantSquare` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerScalarRestriction` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerStratumChart` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerStratumScalarMaps` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerStratumScalarMateDetection` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerSuccessiveDescent` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.KummerTermMate` | unclaimed | Same signatures, instances and public imports; no adaptation. |
| `Sheaf.Paper.TameStratumKummerDescent` | unclaimed | Same signatures, instances and public imports; no adaptation. |

## Status

landed 20261024T021055-L-2707074 2026-10-24 (merge of deliver/V5/Sheaf.Paper.KummerCechDescent)
