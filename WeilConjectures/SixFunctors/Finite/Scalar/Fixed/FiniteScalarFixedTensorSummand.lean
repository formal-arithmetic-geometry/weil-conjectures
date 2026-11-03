/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarComplexTensorPullback

/-! Coproduct summands of fixed-coefficient tensor pullback.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-fixed-tensor-summand).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat
attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive
attribute [local irreducible] sfIntrinsicModuleEquivalence
  SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

private theorem fixedTensor_ι
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    (L : C ⥤ D) [L.Additive] [L.IsLeftAdjoint] [L.Monoidal]
    (P Q : CochainComplex C ℤ) (a b n : ℤ) (h : a + b = n) :
    L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor C) a b n h) ≫
        ((finiteScalarComplexTensorPullbackForFunctor L).app (P, Q)).f n =
      Functor.OplaxMonoidal.δ L (P.X a) (Q.X b) ≫
        CochainComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
          ((L.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) a b n h := by
  simp only [finiteScalarComplexTensorPullbackForFunctor_app,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans L) (.up ℤ) P Q a b n h

private theorem coefficients_ι
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex (Sheaf (ProEt.topology Y) B) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (ProEtale.upperStar B p).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h) ≫
      ((finiteScalarFixedComplexTensorPullbackForCoefficients B p).app (P, Q)).f n =
    Functor.OplaxMonoidal.δ (ProEtale.upperStar B p) (P.X a) (Q.X b) ≫
      CochainComplex.ιMapBifunctor
        (((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj P)
        (((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor _) a b n h := by
  unfold finiteScalarFixedComplexTensorPullbackForCoefficients
  exact fixedTensor_ι (ProEtale.upperStar B p) P Q a b n h

/-- On each coproduct summand, fixed-coefficient tensor pullback is its ordinary tensorator.
Source: Stacks Tag 07A4 and the coproduct-injection formula for mapBifunctorComparison.
(blueprint: lem-sf-finite-scalar-fixed-tensor-summand).

Proof: for an abstract additive monoidal left adjoint, use the defining coproduct-injection
formula of its total comparison. First specialize to sheaves over an abstract coefficient
category, and then to the actual module coefficients. -/
theorem finiteScalarFixedComplexTensorPullback_ι (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h) ≫
      ((finiteScalarFixedComplexTensorPullbackForCoefficients
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).app (P, Q)).f n =
    Functor.OplaxMonoidal.δ
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) (P.X a) (Q.X b) ≫
      CochainComplex.ιMapBifunctor
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P)
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj Q) (curriedTensor _) a b n h := by
  exact coefficients_ι (ModuleCat.{u + 1} (ULift.{u + 1} R)) p P Q a b n h

end WeilConjectures
