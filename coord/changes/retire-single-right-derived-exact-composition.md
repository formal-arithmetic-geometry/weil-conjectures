# CategoryTheory.Functor.single_rightDerived_exact_composition

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition` in favor
of `WeilConjectures.AlgebraicGeometry.SingleRightDerivedExactComposition`, as requested by
`coord/retire-items.tsv` and the human's retirement hand-off. Both already prove the same
canonical equality. The upstream version needs K-injective resolutions only on C, whereas
the copy declares them also on A. Applying the upstream theorem proves the old statement
without changing any canonical map, target, definition, or unit route.

The source-library module stays byte-for-byte unchanged. The DAG Lean attachment is
redirected to it. No module currently imports the retired copy, so no consumer adaptation
is necessary. A scratch check imports only the upstream twin, proves the old statement by
`exact F.single_rightDerived_exact_composition T M`, and prints the theorem's axioms.

## Old

Module: `Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition`.
Existing variable context and theorem signature, verbatim:

```lean
variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB} B] [HasKInjectiveResolutions C] [HasKInjectiveResolutions A]

theorem single_rightDerived_exact_composition (F : C ⥤ A) (T : A ⥤ B)
    [F.Additive] [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (M : C) :
    (T.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
      T.mapDerivedCategory.map
        (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
          F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
            ((CochainComplex.singleFunctor C 0).obj M))) ≫
      (rightDerivedFunctorCompMapDerivedCategoryIso F T).inv.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))
```

## New

Module: `WeilConjectures.AlgebraicGeometry.SingleRightDerivedExactComposition`.
Existing variable context and theorem signature, verbatim:

```lean
variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB} B] [HasKInjectiveResolutions C]

theorem single_rightDerived_exact_composition (F : C ⥤ A) (T : A ⥤ B)
    [F.Additive] [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (M : C) :
    (T.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
      T.mapDerivedCategory.map
        (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
          F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
            ((CochainComplex.singleFunctor C 0).obj M))) ≫
      (rightDerivedFunctorCompMapDerivedCategoryIso F T).inv.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))
```

The duplicate file is withdrawn through `deleted.txt`; the delivery tool writes the
standard empty module. The upstream declaration is the sole retained implementation.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition --uses
CategoryTheory.Functor.single_rightDerived_exact_composition` reports zero downstream
modules and only the copy's own declaration as a textual use. A full source search agrees.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition | R4 | Withdraw duplicate. |
| WeilConjectures.AlgebraicGeometry.SingleRightDerivedExactComposition | unchanged | Retain theorem and proof verbatim; redirect DAG attachment here. |
| WeilConjectures.AlgebraicGeometry.FiniteExactHomSingleCounitTransport | unchanged | Already imports and uses upstream theorem; checked without edits. |

The hand-off's former consumer `Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport`
has already been retired and is absent from the current source tree. There are no forced
adaptations. No target statement or definition changes meaning; no target review reopens.

## Status

landed 20261020T144302-L-2261553 2026-10-20 (merge of deliver/R4/Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition)
