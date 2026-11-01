/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence

/-! # The unit coordinate of finite purity-source reduction

Source: finite smooth coefficient balancing, compatibility (3).
(blueprint: lem-pur-finite-source-unit-reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  Functor.rightAdjoint Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

private theorem unitReductionHom {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (phi : A →+* B) (Y : Scheme.{u})
    (eA : (comparison A Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory A Y))
    (heA : eA = ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
    (eB : (comparison B Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory B Y))
    (heB : eB = ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso B Y)
    (s : comparison A Y ⋙ proScalar phi Y ≅ ordinaryScalar phi Y ⋙ comparison B Y)
    (hs : s = ProEtale.pbcComparisonReduction Y phi) :
    ((proScalar phi Y).mapIso
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).symm ≪≫
      (ProEtale.pbcComparisonReduction Y phi).app (𝟙_ _) ≪≫
      (comparison B Y).mapIso (Etale.ExceptionalCoefficients.unitIso phi Y) ≪≫
      ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso B Y).hom =
      (proScalar phi Y).map eA.inv ≫ s.hom.app (𝟙_ _) ≫
        (comparison B Y).map (Etale.ExceptionalCoefficients.unitIso phi Y).hom ≫ eB.hom := by
  subst heA heB hs
  rfl

private theorem unitSourceInv (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Etale.DerivedCategoryModule A X)
    (eA : (comparison A Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory A Y))
    (heA : eA = ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
    (uA : (puritySource A f L).obj (𝟙_ _) ≅ L)
    (huA : uA = ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app L ≪≫
        Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X L) :
    ((proSource A f L).mapIso
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).symm ≪≫
      (sourceAtOriginIso A f L (𝟙_ _)).symm ≪≫
      (comparison A X).mapIso
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app _ ≪≫
          Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X _)).inv =
      (comparison A X).map uA.inv ≫ (sourceAtOriginIso A f L (𝟙_ _)).hom ≫
        (proSource A f L).map eA.hom := by
  subst heA huA
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]

private theorem unitSourceHom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Etale.DerivedCategoryModule A X)
    (eA : (comparison A Y).obj (𝟙_ _) ≅ 𝟙_ (proCategory A Y))
    (heA : eA = ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
    (uA : (puritySource A f L).obj (𝟙_ _) ≅ L)
    (huA : uA = ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app L ≪≫
        Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X L) :
    ((proSource A f L).mapIso
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).symm ≪≫
      (sourceAtOriginIso A f L (𝟙_ _)).symm ≪≫
      (comparison A X).mapIso
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app _ ≪≫
          Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X _)).hom =
      (proSource A f L).map eA.inv ≫ (sourceAtOriginIso A f L (𝟙_ _)).inv ≫
        (comparison A X).map uA.hom := by
  subst heA huA
  rfl

end AlgebraicGeometry.Scheme.PurityIntegralTower
