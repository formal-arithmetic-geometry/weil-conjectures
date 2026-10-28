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

/-- The normalized étale Hom shift data except for the left comparison equation.
Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact-shift-data`, proof steps 1--2.

The K-injective and flat-term K-flat model construction supplies both normalized
Hom shifts, both composite shift structures, the right component equation, and
the reversed triangulated structures.  The omitted left component equation is
the definitional composition formula proved in the parent module.
(blueprint: lem-coef-etale-hom-transpose-exact-shift-core) -/
theorem etaleHomComparison_reversedExact_shiftCore
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X) :
    letI := etaleHomScalarCommShift X φ
    ∃ (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
      (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
        ((scalarExtension φ X).obj M)).CommShift ℤ),
      EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA ∧
      EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X ((scalarExtension φ X).obj M) sB ∧
      (letI : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
          ((scalarExtension φ X).obj M)).CommShift ℤ := sB
       letI : (scalarExtension φ X).op.CommShift ℤ :=
         Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)
       letI : (EtaleHomRight X φ M).CommShift ℤ :=
         @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
           (Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)) sB
       ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
          ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
              ((scalarExtension φ X).obj M)).map
            ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) ∧
      (letI : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ := sA
       letI : (EtaleHomLeft X φ M).CommShift ℤ :=
         @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ sA
           (etaleHomScalarCommShift X φ)
       (EtaleHomLeft X φ M).IsTriangulated) ∧
      (letI : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
          ((scalarExtension φ X).obj M)).CommShift ℤ := sB
       letI : (scalarExtension φ X).op.CommShift ℤ :=
         Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)
       letI : (EtaleHomRight X φ M).CommShift ℤ :=
         @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
           (Pretriangulated.Opposite.commShiftFunctorOpInt (scalarExtension φ X)) sB
       (EtaleHomRight X φ M).IsTriangulated) := by
  sorry

end AlgebraicGeometry.Etale
