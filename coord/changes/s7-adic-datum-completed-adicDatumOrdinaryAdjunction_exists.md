# AlgebraicGeometry.Scheme.adicDatumOrdinaryAdjunction_exists

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

## Old

```lean
theorem adicDatumOrdinaryAdjunction_exists :
    ∃ adj : completedConstantExtension T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ M : completedConstantModules T R, adj.unit.app M = adicDatumOrdinaryUnit T φ M
```

## New

```lean
theorem adicDatumOrdinaryAdjunction_exists :
    ∃ adj : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ M : completedConstantModules T R, adj.unit.app M = adicDatumOrdinaryUnit T φ M
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
