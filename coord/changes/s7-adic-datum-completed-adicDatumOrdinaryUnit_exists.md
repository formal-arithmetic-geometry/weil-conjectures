# AlgebraicGeometry.Scheme.adicDatumOrdinaryUnit_exists

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

## Old

```lean
theorem adicDatumOrdinaryUnit_exists (M : completedConstantModules T R) :
    ∃! u : M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((completedConstantExtension T φ).obj M),
      ∀ (U : T.ProEtᵒᵖ) (m : M.val.obj U),
        u.val.app U m = adicDatumTensorSection T φ M U 1 m
```

## New

```lean
theorem adicDatumOrdinaryUnit_exists (M : completedConstantModules T R) :
    ∃! u : M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((reductionChange T φ).obj M),
      ∀ (U : T.ProEtᵒᵖ) (m : M.val.obj U),
        u.val.app U m = adicDatumTensorSection T φ M U 1 m
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Definitionally equal statement; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
