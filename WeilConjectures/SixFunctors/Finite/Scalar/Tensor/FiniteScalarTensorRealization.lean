/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDescent

/-! # Unique normalized derived scalar tensor realization

Source: Stacks Tags 07A4 and 04VK.
(blueprint: lem-sf-finite-scalar-tensor-realization).
 -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

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

/-- Apply representative descent before specializing the intrinsic ring sheaf.
Source: Stacks 07A4 and 04VK
(blueprint: lem-sf-finite-scalar-tensor-realization). -/
@[irreducible] def finiteScalarTensorRealizationForModels
    (B : Type u₁) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (Rₛ : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : CochainComplex (Sheaf (ProEt.topology T) B) ℤ ⥤
      CochainComplex (proEtaleRingModules T Rₛ) ℤ)
    (LF : DerivedCategory (Sheaf (ProEt.topology T) B) ⥤
      DerivedCategory (proEtaleRingModules T Rₛ))
    (eps : DerivedCategory.Q ⋙ LF ≅ F ⋙ DerivedCategory.Q)
    (P : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hP : ∀ Q, P Q → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hF : ∀ Q, P Q → proEtaleFlatRepresentatives T Rₛ (F.obj Q))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (Sheaf (ProEt.topology T) B) ×
        DerivedCategory (Sheaf (ProEt.topology T) B))
      (DerivedCategory (proEtaleRingModules T Rₛ))).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful)
    (a : ProEtaleTensorModel T Rₛ)
    (b : uncurry.obj ((curriedTensor (Sheaf (ProEt.topology T) B)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ F ≅
      (F.prod F) ⋙ uncurry.obj ((proEtaleOrdinaryTensor T Rₛ).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))) :
    (postcompose₂.obj LF).obj (ProEtale.derivedTensor B T) ≅
      (((whiskeringLeft₂ _).obj LF).obj LF).obj (curry.obj a.tensor) :=
  finiteScalarTensorRealizationForCoefficients B T DerivedCategory.Q F LF eps P hP
    (proEtaleFlatRepresentatives T Rₛ) hF ff _ a.tensor a.representative b

/-- Construct signed totalization before specializing the coefficient category.
Source: Stacks 06YN and 07A4
(blueprint: lem-sf-finite-scalar-tensor-realization). -/
@[irreducible] def finiteScalarTensorRealizationForOrdinaryModels
    (B : Type u₁) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (Rₛ : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : Sheaf (ProEt.topology T) B ⥤ proEtaleRingModules T Rₛ)
    [F.Additive] [F.IsEquivalence]
    (LF : DerivedCategory (Sheaf (ProEt.topology T) B) ⥤
      DerivedCategory (proEtaleRingModules T Rₛ))
    (eps : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hP : ∀ Q, P Q → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hF : ∀ Q, P Q → proEtaleFlatRepresentatives T Rₛ
      ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (ff : ((whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (Sheaf (ProEt.topology T) B) ×
        DerivedCategory (Sheaf (ProEt.topology T) B))
      (DerivedCategory (proEtaleRingModules T Rₛ))).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))).FullyFaithful)
    (a : ProEtaleTensorModel T Rₛ)
    (b : tensor (Sheaf (ProEt.topology T) B) ⋙ F ≅
      (F.prod F) ⋙ @tensor (proEtaleRingModules T Rₛ) _
        (SheafOfModules.monoidalCategory Rₛ)) :
    (postcompose₂.obj LF).obj (ProEtale.derivedTensor B T) ≅
      (((whiskeringLeft₂ _).obj LF).obj LF).obj (curry.obj a.tensor) :=
  letI := SheafOfModules.monoidalCategory Rₛ
  finiteScalarTensorRealizationForModels B T Rₛ (F.mapHomologicalComplex (.up ℤ))
    LF eps P hP hF ff a (finiteScalarTotalTensorIsoOfOrdinary F b)

/-- The normalized tensor realization in the curried notation used by projection mates.
Source: Stacks 07A4 (blueprint: lem-sf-finite-scalar-tensor-realization). -/
@[irreducible] def finiteScalarTensorRealization
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (a : ProEtaleTensorModel T (proEtaleConstantRing T R)) :
    (postcompose₂.obj (sfIntrinsicDerivedEquivalence T R).functor).obj
        (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} R)) T) ≅
      (((whiskeringLeft₂ _).obj (sfIntrinsicDerivedEquivalence T R).functor).obj
        (sfIntrinsicDerivedEquivalence T R).functor).obj (curry.obj a.tensor) :=
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T R))
  finiteScalarTensorRealizationForOrdinaryModels
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) T (proEtaleConstantRing T R)
    (sfIntrinsicModuleEquivalence T R).functor
    (sfIntrinsicDerivedEquivalence T R).functor
    (sfIntrinsicModuleEquivalence T R).functor.mapDerivedCategoryFactors
    (finiteScalarFlatRepresentatives T R) (finiteScalarFlatRepresentatives_kFlat T R)
    (finiteScalarPreservesRepresentatives T R)
    (Classical.choice (finiteScalarRepresentativesFullyFaithful T R)) a
    (finiteScalarOrdinaryTensorIso T R)

end WeilConjectures
