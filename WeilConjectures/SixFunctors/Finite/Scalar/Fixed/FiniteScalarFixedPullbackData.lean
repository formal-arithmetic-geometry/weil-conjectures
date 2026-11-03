/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Fixed.FiniteScalarFixedTensorData
public import WeilConjectures.SixFunctors.Finite.Scalar.Fixed.FiniteScalarFixedTensorPullbackNormalization

/-! # Native fixed pullback presentation data

Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-fixed-pullback-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
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

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarFixedTensorDataForCoefficients

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- Store the native fixed pullback comparison before scalar realization.
Source: Stacks Tag 07A4 (blueprint: lem-sf-finite-scalar-fixed-pullback-data). -/
noncomputable def finiteScalarFixedPullbackDataForCoefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [ProEtale.UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (S : ObjectProperty (CochainComplex (Sheaf (ProEt.topology Y) B) ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (T : ObjectProperty (CochainComplex (Sheaf (ProEt.topology X) B) ℤ))
    (hT : ∀ Z, T Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (hA : ∀ Z, S Z → T (((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj Z))
    (f : DerivedCategory.Q ⋙ (ProEtale.upperStar B p).leftDerivedFunctor ≅
      (ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    TensorFixedPullbackData (finiteScalarFixedTensorDataForCoefficients B Y S hS)
      (finiteScalarFixedTensorDataForCoefficients B X T hT) where
  A := (ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)
  F := (ProEtale.upperStar B p).leftDerivedFunctor
  f := f
  hA := hA
  mF := finiteScalarFixedComplexTensorPullbackForCoefficients B p
  phiF := ProEtale.leftDerivedUpperStarTensorComparison B p

/-- The native fixed pullback data obey their representative law over abstract coefficients.
Source: Stacks Tag 07A4 (blueprint: lem-sf-finite-scalar-fixed-pullback-data).

Proof: unfold the two data records and apply the proved native tensor pullback
normalization with the supplied factors-to-counit equation and preservation proof. -/
theorem finiteScalarFixedPullbackDataForCoefficients_law
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [ProEtale.UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (S : ObjectProperty (CochainComplex (Sheaf (ProEt.topology Y) B) ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (T : ObjectProperty (CochainComplex (Sheaf (ProEt.topology X) B) ℤ))
    (hT : ∀ Z, T Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (hA : ∀ Z, S Z → T (((ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ)).obj Z))
    (f : DerivedCategory.Q ⋙ (ProEtale.upperStar B p).leftDerivedFunctor ≅
      (ProEtale.upperStar B p).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hf : ∀ Z, f.hom.app Z = (ProEtale.upperStar B p).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj Z)) :
    (finiteScalarFixedPullbackDataForCoefficients B p S hS T hT hA f).law := by
  dsimp only [TensorFixedPullbackData.law, finiteScalarFixedPullbackDataForCoefficients,
    finiteScalarFixedTensorDataForCoefficients]
  intro P Q hp hq
  exact finiteScalarTensorPullback_normalizationForCoefficients B p S hS T hT f hf
    P Q hp hq (hA P hp) (hA Q hq)

end WeilConjectures
