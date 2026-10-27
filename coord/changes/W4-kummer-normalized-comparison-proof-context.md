# Kummer normalized comparison proof context

## Reason

The initial compile exceeded the single-file 60-second limit. Concrete inverse
and direct image functors can expand their sheaf and coefficient constructions
during elaboration. Keep `upperStar` and `lowerStar` locally irreducible, using
the same established elaboration boundary as `KummerCechDescent`. This is a local
proof context only: no exported reducibility attribute or definition body changes.

## Old

No local reducibility commands before the namespace. Existing definitions,
public signatures, public imports and instance registrations are unchanged.

## New

```lean
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
```

The original `kummerAlternating_additive` docstring is also prefixed by
`set_option linter.unusedSectionVars false in`, because its unchanged signature
retains the commutativity instance that the componentwise proof does not use.
These commands are local to this file and require no consumer adaptations.
No target statement or meaning changes.

## Users

The following consumers are reported by `tools/downstream.py
Sheaf.Paper.KummerNormalizedComparison`. Holder values use the current local
claim records; none of these modules is edited.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.KummerBarResolution` | U4 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerChartGeometryMaps` | V2 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerCoefficientModels` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerCoherentRoof` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerConstantNerveTerm` | V3 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerGeometricColumns` | V4 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerGlobalChart` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerInvariantScalarMap` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerLocalSource` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerNerveGeometricMap` | W3 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerNerveTransport` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerNormalizedChart` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerParameterizedTerm` | X2 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveChart` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveCoordinates` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveMorphism` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveNaturality` | J6 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveScalarMorphism` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerRefinement` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerResolutionColumns` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerResolvedDescent` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerScalarInvariantSquare` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerScalarRestriction` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerStratumChart` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerStratumScalarMaps` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerStratumScalarMateDetection` | F2 | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerSuccessiveDescent` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.KummerTermMate` | unclaimed | Unchanged interface and constructions; no adaptation. |
| `Sheaf.Paper.TameStratumKummerDescent` | K1 | Unchanged interface and constructions; no adaptation. |

## Status

landed 20261025T061101-L-2396327 2026-10-25 (merge of deliver/W4/Sheaf.Paper.KummerNormalizedComparison)
