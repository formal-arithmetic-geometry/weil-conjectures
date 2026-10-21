# AlgebraicGeometry.Scheme.adicDatumAdjunction_exists

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

## Old

```lean
theorem adicDatumAdjunction_exists :
    ∃ adj : adicDatumExtension T φ ⊣ adicDatumRestriction T φ,
      ∀ (C : HomotopyCategory (completedConstantModules T R) (ComplexShape.up ℤ))
        (D : HomotopyCategory (completedConstantModules T S) (ComplexShape.up ℤ))
        (f : ((completedConstantExtension T φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj C ⟶ D),
        adj.homEquiv ((adicDatumQh T R).obj C) ((adicDatumQh T S).obj D)
          ((adicDatumExtensionCounit T φ).app C ≫ (adicDatumQh T S).map f) =
        (adicDatumQh T R).map
          ((adicDatumOrdinaryAdjunction T φ).mapHomotopyCategory (ComplexShape.up ℤ)
            |>.homEquiv C D f) ≫ (adicDatumRestrictionComparison T φ).inv.app D
```

## New

```lean
theorem adicDatumAdjunction_exists :
    ∃ adj : adicDatumExtension T φ ⊣ adicDatumRestriction T φ,
      ∀ (C : HomotopyCategory (completedConstantModules T R) (ComplexShape.up ℤ))
        (D : HomotopyCategory (completedConstantModules T S) (ComplexShape.up ℤ))
        (f : ((reductionChange T φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj C ⟶ D),
        adj.homEquiv ((adicDatumQh T R).obj C) ((adicDatumQh T S).obj D)
          ((adicDatumExtensionCounit T φ).app C ≫ (adicDatumQh T S).map f) =
        (adicDatumQh T R).map
          ((adicDatumOrdinaryAdjunction T φ).mapHomotopyCategory (ComplexShape.up ℤ)
            |>.homEquiv C D f) ≫ (adicDatumRestrictionComparison T φ).inv.app D
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |

| Sheaf.Paper.CompletedKoszulReductionRoosTriangle | unclaimed | Docstring citation of the same normalized adjunction; no source adaptation. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
