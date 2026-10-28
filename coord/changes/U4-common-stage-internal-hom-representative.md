# SpecifiedHomScalarRational_tower import

## Reason

The representative transport proof needs the existing coefficient-level theorem
`specifiedHomScalarRational_tower`. Its original public import of
`Sheaf.Paper.DerivedPullbackTensorHom` creates a cycle when used from
`Sheaf.Paper.CommonStageInternalHomRepresentative`, because the derived pullback module imports
the common-stage Hom descent chain. The theorem itself only uses finite rational operations and
normalized coefficient-stage declarations.

## Old

```lean
public import Sheaf.Paper.DerivedPullbackTensorHom
```

## New

```lean
public import Sheaf.Paper.FiniteRationalDerivedOperations
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Compiles unchanged; it receives the same theorem declaration and its own imports provide the downstream definitions it uses. |
| Sheaf.Paper.CommonStageInternalHomRepresentative | U4 | Can import the theorem without closing an import cycle. |

## Status

landed 20261028T020810-L-2549446 2026-10-28 (merge of deliver/U4/Sheaf.Paper.CommonStageInternalHomRepresentative)
