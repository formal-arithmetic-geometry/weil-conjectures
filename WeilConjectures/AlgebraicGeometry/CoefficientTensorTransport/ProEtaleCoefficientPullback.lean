/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels

/-! # Normalization of exact derived coefficient pullback

(blueprint: lem-pbc-coefficient-pullback-factorization)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
attribute [local instance]
  AlgebraicGeometry.Scheme.proEtaleRingRestrictionPullbackInv_isIso
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.pbcDerivedRestrict
  SheafOfModules.restrictScalars
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  AlgebraicGeometry.Scheme.proEtaleRingDerivedPullbackFactors SheafOfModules.monoidalCategory

namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

/-- Signed direct-sum total tensor on complexes, before localization. -/
abbrev total (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  Functor.uncurry.obj ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The canonical ordinary restriction/pullback comparison with base identity removed. -/
def ordinaryPullback :
    proEtaleRingModulePullback f R S c ⋙ pbcRestrict c.hom ≅
      proEtaleRingModulePullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
  (asIso (proEtaleRingRestrictionPullbackInv f R R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
    (𝟙 R) c.hom (Iso.refl _) c (by simp))).symm ≪≫
    isoWhiskerRight (Iso.refl _) _ ≪≫ Functor.leftUnitor _

/-- Its termwise comparison on cochain complexes. -/
def complexPullback :
    (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ) ⋙
        (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ) ≅
      (proEtaleRingModulePullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (ordinaryPullback f R S c) (.up ℤ)

end AlgebraicGeometry.Scheme.CoefficientTensorChain

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Exact derived restriction along the identity, identified with the identity functor.
Source: functoriality of exact derived functors; Stacks Tag 07A6. -/
def identityRestriction : pbcDerivedRestrict (𝟙 R) ≅
    𝟭 (DerivedCategory (proEtaleRingModules Y R)) :=
  Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryIdIso (proEtaleRingModules Y R)

/-- The canonical pullback comparison, with identity restriction on the base removed.
Source: Stacks Tags 0D6D and 07A6. -/
def pullback :
    proEtaleRingDerivedPullback f R S c ⋙ pbcDerivedRestrict c.hom ≅
      proEtaleRingDerivedPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
  proEtaleRingRestrictionDerivedPullback f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp) ≪≫
    isoWhiskerRight (identityRestriction R) _ ≪≫ Functor.leftUnitor _

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
