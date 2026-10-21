# AlgebraicGeometry.Scheme.adicDatumOrdinaryReduction

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumOrdinaryReduction (n : ℕ) : adicDatumModules T d ⥤ adicDatumModules T d :=
  completedConstantExtension T (adicDatumProjection T d n) ⋙
    SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map (adicDatumProjection T d n))
```

## New

```lean
def adicDatumOrdinaryReduction (n : ℕ) : adicDatumModules T d ⥤ adicDatumModules T d :=
  reductionChange T (adicDatumProjection T d n) ⋙
    SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map (adicDatumProjection T d n))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
