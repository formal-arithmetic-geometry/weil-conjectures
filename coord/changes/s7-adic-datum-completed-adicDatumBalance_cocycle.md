# AlgebraicGeometry.Scheme.adicDatumBalance_cocycle

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

## Old

```lean
theorem adicDatumBalance_cocycle
    {V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (χ : B ⟶ V)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    ((completedConstantExtension T χ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((adicDatumBalance T φ ψ).hom.app C) ≫
      (adicDatumBalance T (φ ≫ ψ) χ).hom.app C =
    (adicDatumBalance T ψ χ).hom.app
        (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      (adicDatumBalance T φ (ψ ≫ χ)).hom.app C ≫
      eqToHom (congrArg (fun ξ ↦
        ((completedConstantExtension T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
          (Category.assoc φ ψ χ).symm)
```

## New

```lean
theorem adicDatumBalance_cocycle
    {V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (χ : B ⟶ V)
    (C : CochainComplex (completedConstantModules T R) ℤ) :
    ((reductionChange T χ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((adicDatumBalance T φ ψ).hom.app C) ≫
      (adicDatumBalance T (φ ≫ ψ) χ).hom.app C =
    (adicDatumBalance T ψ χ).hom.app
        (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      (adicDatumBalance T φ (ψ ≫ χ)).hom.app C ≫
      eqToHom (congrArg (fun ξ ↦
        ((reductionChange T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
          (Category.assoc φ ψ χ).symm)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
