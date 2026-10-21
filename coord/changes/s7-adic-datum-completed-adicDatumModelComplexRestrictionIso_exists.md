# AlgebraicGeometry.Scheme.adicDatumModelComplexRestrictionIso_exists

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

## Old

```lean
theorem adicDatumModelComplexRestrictionIso_exists {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    ∃! e : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
        ((adicDatumTowerFunctor T d).obj M.complex)).obj (op n) ≅
      ((SheafOfModules.restrictScalars.{t + 1}
        ((adicLisseForget T).map (adicDatumProjection T d n))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((completedConstantExtension T (adicDatumProjection T d n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex),
      ∀ i : ℤ, e.hom.f i = 𝟙 _
```

## New

```lean
theorem adicDatumModelComplexRestrictionIso_exists {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    ∃! e : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
        ((adicDatumTowerFunctor T d).obj M.complex)).obj (op n) ≅
      ((SheafOfModules.restrictScalars.{t + 1}
        ((adicLisseForget T).map (adicDatumProjection T d n))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex),
      ∀ i : ℤ, e.hom.f i = 𝟙 _
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
