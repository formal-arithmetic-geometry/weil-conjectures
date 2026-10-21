# AlgebraicGeometry.Scheme.adicDatumBalance_exists

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

## Old

```lean
theorem adicDatumBalance_exists :
    ∃! e : (completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (completedConstantExtension T ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (completedConstantExtension T (φ ≫ ψ)).mapHomologicalComplex (ComplexShape.up ℤ),
      ∀ (C : CochainComplex (completedConstantModules T R) ℤ) (p : ℤ) (U : T.ProEtᵒᵖ)
        (s : B.obj.obj U) (r : S.obj.obj U) (x : (C.X p).val.obj U),
        ((e.hom.app C).f p).val.app U
          (adicDatumTensorSection T ψ ((completedConstantExtension T φ).obj (C.X p)) U s
            (adicDatumTensorSection T φ (C.X p) U r x)) =
        adicDatumTensorSection T (φ ≫ ψ) (C.X p) U
          (s * ψ.hom.app U r) x
```

## New

```lean
theorem adicDatumBalance_exists :
    ∃! e : (reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (reductionChange T ψ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (reductionChange T (φ ≫ ψ)).mapHomologicalComplex (ComplexShape.up ℤ),
      ∀ (C : CochainComplex (completedConstantModules T R) ℤ) (p : ℤ) (U : T.ProEtᵒᵖ)
        (s : B.obj.obj U) (r : S.obj.obj U) (x : (C.X p).val.obj U),
        ((e.hom.app C).f p).val.app U
          (adicDatumTensorSection T ψ ((reductionChange T φ).obj (C.X p)) U s
            (adicDatumTensorSection T φ (C.X p) U r x)) =
        adicDatumTensorSection T (φ ≫ ψ) (C.X p) U
          (s * ψ.hom.app U r) x
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
