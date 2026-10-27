# WeilConjectures.purAdicReductionShift_existsUnique

## Reason

The reduction-shift proof requires a local boundary around large categorical definitions.
Unfolding the standard derived-category witness and selected scalar reduction packages
caused single-file elaboration to exceed 60 seconds. The named witnesses suffice instead.
All existing public signatures, public imports and definition bodies are verbatim.
The new helper is private and fully proved. No consumer needs adaptation.

## Old

The original file has no local irreducibility attributes for these definitions.
The original reduction-shift theorem proof is `by sorry`.

## New

```lean
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
```

The reduction-shift theorem body is complete. The finite-source theorem remains its
original named `by sorry`. Definition bodies selecting both unique comparisons are
unchanged. No target statement review is reopened.

## Users

The downstream scan lists the following modules. A separate uses scan finds no use of
IsPurAdicFiniteSourceIdentification outside its own module. The local attributes and
options are absent from the imported interface; every consumer keeps its existing
statements and proof elaboration environment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicNormalizedPurityLift | P3 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | R4 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | B7 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | S2 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Identical public interface and definitions; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Identical public interface and definitions; no adaptation. |

## Status

landed 20261025T101138-L-3661831 2026-10-25 (merge of deliver/H9/Sheaf.Paper.AdicPuritySourceReduction)
