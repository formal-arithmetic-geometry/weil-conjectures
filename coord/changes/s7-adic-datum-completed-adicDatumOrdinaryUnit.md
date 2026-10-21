# AlgebraicGeometry.Scheme.adicDatumOrdinaryUnit

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumOrdinaryUnit (M : completedConstantModules T R) :
    M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((completedConstantExtension T φ).obj M) :=
  (adicDatumOrdinaryUnit_exists T φ M).exists.choose
```

## New

```lean
def adicDatumOrdinaryUnit (M : completedConstantModules T R) :
    M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((reductionChange T φ).obj M) :=
  (adicDatumOrdinaryUnit_exists T φ M).exists.choose
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
