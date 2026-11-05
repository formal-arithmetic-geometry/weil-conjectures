/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The restricted derived scalar mate on representatives

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-mate-restriction-counit-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
universe u₀ v₀ w₀
section
variable {A B A' B' : Type u₀}
  [Category.{v₀} A] [Category.{v₀} B] [Category.{v₀} A'] [Category.{v₀} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w₀} B]
  [HasDerivedCategory.{w₀} A'] [HasDerivedCategory.{w₀} B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  (ad : L ⊣ R.mapDerivedCategory.{w₀, w₀}) (ad' : L' ⊣ R'.mapDerivedCategory.{w₀, w₀})
  (ε : DerivedCategory.Q.{w₀} ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w₀})
  (ε' : DerivedCategory.Q.{w₀} ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w₀})
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R')
  (ρd : R.mapDerivedCategory.{w₀, w₀} ⋙ F.mapDerivedCategory.{w₀, w₀} ≅
    G.mapDerivedCategory.{w₀, w₀} ⋙ R'.mapDerivedCategory.{w₀, w₀})
  (hρ : ∀ K : CochainComplex B ℤ,
    ρd.hom.app (DerivedCategory.Q.{w₀}.obj K) ≫
      R'.mapDerivedCategory.{w₀, w₀}.map (G.mapDerivedCategoryFactors.{w₀, w₀}.hom.app K) ≫
      R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategory.{w₀, w₀}.map (R.mapDerivedCategoryFactors.{w₀, w₀}.hom.app K) ≫
      F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.{w₀}.map ((NatTrans.mapHomologicalComplex ρ.hom (.up ℤ)).app K))
  (e : E ⋙ G ≅ F ⋙ E')
  (β : F.mapDerivedCategory.{w₀, w₀} ⋙ L' ⟶ L ⋙ G.mapDerivedCategory.{w₀, w₀})
  (hβ : ∀ X, ad'.unit.app (F.mapDerivedCategory.{w₀, w₀}.obj X) ≫
    R'.mapDerivedCategory.{w₀, w₀}.map (β.app X) =
    F.mapDerivedCategory.{w₀, w₀}.map (ad.unit.app X) ≫
      ρd.hom.app (L.obj X))
  (P : CochainComplex A ℤ)
  (hunit : ad.unit.app (DerivedCategory.Q.{w₀}.obj P) ≫
    R.mapDerivedCategory.{w₀, w₀}.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.{w₀, w₀}.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.{w₀}.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ad'.unit.app (DerivedCategory.Q.{w₀}.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    R'.mapDerivedCategory.{w₀, w₀}.map (ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
      ((E'.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Q.{w₀}.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))

end

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint
  proEtaleRingModulePullback
  SheafOfModules.monoidalCategory ordinaryComplexIso ordinaryTensorIso
  proEtaleRingRestrictionDerivedPullback
set_option backward.defeqAttrib.useBackward true

end AlgebraicGeometry.Scheme.DerivedScalarMate
