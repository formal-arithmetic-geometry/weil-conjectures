/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.EtaleHomComparisonModels

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

/-- The normalized shifts and exact functor structures needed by the étale Hom comparison.
Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact`, proof steps 1--2.

The proof constructs K-injective and flat-term K-flat models, transports the signed
source reindexing through evaluation, and applies the cone calculation for internal Hom.
This is the shift and functor-exactness part of the parent comparison theorem.
(blueprint: lem-coef-etale-hom-transpose-exact-shift-data) -/
theorem etaleHomComparison_reversedExact_shiftData
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X) :
    letI := etaleHomScalarCommShift X φ
    ∃ (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
      (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
        ((scalarExtension φ X).obj M)).CommShift ℤ)
      (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
      (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ),
      EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA ∧
      EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X ((scalarExtension φ X).obj M) sB ∧
      (∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomLeft X φ M).commShiftIso n).hom.app (op K) =
          (scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
            ((scalarExtension φ X).commShiftIso n).hom.app
              (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))) ∧
      (∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
          ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
              ((scalarExtension φ X).obj M)).map
            ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) ∧
      (EtaleHomLeft X φ M).IsTriangulated ∧
      (EtaleHomRight X φ M).IsTriangulated := by
  sorry

end AlgebraicGeometry.Etale
