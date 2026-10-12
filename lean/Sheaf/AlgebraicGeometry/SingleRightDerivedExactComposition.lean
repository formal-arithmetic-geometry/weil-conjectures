/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Canonical single comparison under exact postcomposition

Source: Stacks Project, Tag 0AVW, canonical affine factorization.
(blueprint: lem-sc-single-right-derived-exact-composition).
-/

@[expose] public section

universe uC uA uB vC vA vB wC wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB} B] [HasKInjectiveResolutions C] [HasKInjectiveResolutions A]

/-- The canonical single-to-right-derived comparison commutes with exact postcomposition.
Source: Stacks Project, Tag 0AVW, canonical factorization of affine pushforward
(blueprint: lem-sc-single-right-derived-exact-composition).

Proof: Expand the comparison for the composite right-derived functor. Uniqueness of
right derived functors identifies its composite with the composite of the two units.
Postcomposing the second unit with its exact-functor comparison gives the inverse
localization comparison. Naturality of that comparison moves the inverse single map
through it. The termwise single comparisons compose, leaving the canonical single
comparison for F followed by T. This is an equality of canonical maps, valid also for
zero objects and zero functors. -/
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
        ((CochainComplex.singleFunctor C 0).obj M))  := by sorry

end CategoryTheory.Functor
