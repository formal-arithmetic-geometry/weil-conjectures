/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorOrdinaryModelRepresentativeEquation

/-! # Representative equation with the fixed scalar source

Source: Stacks Project, Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-scalar-source-model-representative-equation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor MonoidalCategory
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

universe u
namespace WeilConjectures

/-- The ordinary-model representative equation with the fixed scalar source
category and its specified representative class, before specializing F or LF.
Proof: specialize the proved ordinary-model equation to the module coefficient
category and the fixed flat-term K-flat representatives. All comparisons are unchanged.
Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-scalar-source-model-representative-equation). -/
theorem finiteScalarTensorRealizationForScalarSourceModels_representative
    (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u})
    (Rₛ : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)) ⥤ proEtaleRingModules T Rₛ)
    [F.Additive] [F.IsEquivalence]
    (LF : DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ⥤
      DerivedCategory (proEtaleRingModules T Rₛ))
    (eps : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hF : ∀ Q, (finiteScalarFlatRepresentatives T R) Q → proEtaleFlatRepresentatives T Rₛ
      ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (ff : ((whiskeringLeft
      ((finiteScalarFlatRepresentatives T R).FullSubcategory ×
        (finiteScalarFlatRepresentatives T R).FullSubcategory)
      (DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ×
        DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))))
      (DerivedCategory (proEtaleRingModules T Rₛ))).obj
      (((finiteScalarFlatRepresentatives T R).ι ⋙ DerivedCategory.Q).prod
        ((finiteScalarFlatRepresentatives T R).ι ⋙ DerivedCategory.Q))).FullyFaithful)
    (a : ProEtaleTensorModel T Rₛ)
    (b : tensor (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ⋙ F ≅
      (F.prod F) ⋙ @tensor (proEtaleRingModules T Rₛ) _
        (SheafOfModules.monoidalCategory Rₛ))
    (X Z : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hx : (finiteScalarFlatRepresentatives T R) X) (hz : (finiteScalarFlatRepresentatives T R) Z) :
    letI := SheafOfModules.monoidalCategory Rₛ
    LF.map ((finiteScalarFixedTensorRepresentativeForCoefficients
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) T (finiteScalarFlatRepresentatives T R)
      (finiteScalarFlatRepresentatives_kFlat T R)).hom.app
        (⟨X, hx⟩, ⟨Z, hz⟩)) ≫
      ((finiteScalarTensorRealizationForOrdinaryModels
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) T Rₛ F LF eps
        (finiteScalarFlatRepresentatives T R) (finiteScalarFlatRepresentatives_kFlat T R)
        hF ff a b).hom.app
        (DerivedCategory.Q.obj X)).app (DerivedCategory.Q.obj Z) ≫
      a.tensor.map (Prod.mkHom (eps.hom.app X) (eps.hom.app Z)) =
    eps.hom.app (CochainComplex.mapBifunctor X Z
      (curriedTensor (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))))) ≫
      DerivedCategory.Q.map ((finiteScalarTotalTensorIsoOfOrdinary F b).hom.app (X, Z)) ≫
      a.representative.hom.app
        (⟨(F.mapHomologicalComplex (.up ℤ)).obj X, hF X hx⟩,
         ⟨(F.mapHomologicalComplex (.up ℤ)).obj Z, hF Z hz⟩) := by
  exact finiteScalarTensorRealizationForOrdinaryModels_representative
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) T Rₛ F LF eps
    (finiteScalarFlatRepresentatives T R) (finiteScalarFlatRepresentatives_kFlat T R)
    hF ff a b X Z hx hz

end WeilConjectures
