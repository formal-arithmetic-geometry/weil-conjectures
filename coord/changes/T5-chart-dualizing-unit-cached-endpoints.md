# chartDualizingUnit

## Reason

Use the existing `smoothPurityUnitIso` wrapper, whose cached source is
`ordinaryFiniteUnit`. Its body is exactly the `Etale.singleFunctorObjUnitIso`
previously used here. Delta reduction therefore gives the identical isomorphism;
no data, statement, normalization or public visibility changes. This avoids
repeated conversion of the expanded constant-sheaf and tensor-unit encodings.
The finite-Tor proof uses the same cached wrapper.

## Old

```lean
def chartDualizingUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f ≅
      P.diagonalOrdinaryDualizing f :=
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).symm
```

## New

```lean
def chartDualizingUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f ≅
      P.diagonalOrdinaryDualizing f :=
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
    (smoothPurityUnitIso P.Coefficient Y).symm
```

## Users

The uses from `tools/downstream.py --uses chartDualizingUnit` were read. The
wrapper delta-reduces to the old body, so every consumer receives the same map
and requires no adaptation. Module and node claims were checked.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | reuse cached endpoint API |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | definitionally identical map |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | definitionally identical map |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | definitionally identical map |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | definitionally identical map |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | definitionally identical map |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | definitionally identical map |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | definitionally identical map |

## Status

landed 20261026T002820-L-117385 2026-10-26 (merge of deliver/T5/Sheaf.Paper.DiagonalDncChartNormalization)
