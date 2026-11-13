/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Ordered.EtaleOrderedOpenProjectionScalarConjugation

/-! # Scalar change for the local ordered open projection

This is the open-immersion square before inserting a compactification pullback compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar openImmersionLowerShriek
  derivedTensor
attribute [local irreducible] derivedTensorSymmetry
  derivedOpenImmersionLowerShriekProjectionIso ExceptionalCoefficients.openIso
  ExceptionalCoefficients.tensorIso scalarPullbackIso
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctorIsoMapDerivedCategory

/-- The ordered open projection, without any composite-pullback identification.
Source: Stacks 0E8I and 0GL6. -/
@[irreducible] def orderedOpenProjection (R : Type (u + 1)) [CommRing R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (T : DerivedCategoryModule R Z) (M : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) Z).obj T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj M) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor.obj T)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Z).inv.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj M)).app T ≫
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} R) j).inv.app M).app T ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app M).app
        ((upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor.obj T))

/-- Scalar change commutes with the local ordered open projection.
Source: Stacks 0E8I, 0GL6 and 07A4. -/
theorem etaleOrderedOpenProjectionScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (T : DerivedCategoryModule A Z) (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).map (orderedOpenProjection A j T M) ≫
      (ExceptionalCoefficients.openIso φ j).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T)).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T, M) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) X).map
            ((scalarPullbackIso φ j).inv.app T)).app ((scalarExtension φ X).obj M)) =
    (ExceptionalCoefficients.tensorIso φ Z).hom.app
        (T, (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) Z).obj
        ((scalarExtension φ Z).obj T)).map
          ((ExceptionalCoefficients.openIso φ j).hom.app M) ≫
      orderedOpenProjection B j ((scalarExtension φ Z).obj T)
        ((scalarExtension φ X).obj M) := by
  have hmix := (etaleOpenScalarComparisons φ j).mixed_tensor_scalar M T
  apply (cancel_mono ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
    (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
      ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
        ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M)))).mp
  exact etaleOrderedOpenProjectionScalar_postcomp φ j T M
    (orderedOpenProjection A j T M)
    (orderedOpenProjection B j ((scalarExtension φ Z).obj T) ((scalarExtension φ X).obj M)) hmix
    (by simp only [orderedOpenProjection]) (by simp only [orderedOpenProjection])

end AlgebraicGeometry.Etale
