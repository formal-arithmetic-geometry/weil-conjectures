/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization

/-! # Representative equation before scalar specialization

Source: Stacks Project, Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-ordinary-model-representative-equation).
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

universe u u₁
namespace WeilConjectures

/-- The normalized tensor realization satisfies its representative equation before
specializing the coefficient category or the ordinary realization functor.

Proof: expand the three staged realization wrappers and apply the proved generic
representative-descent equation with the signed total of the supplied ordinary tensor
comparison. The fixed source representative and the target model representative are
exactly the two representatives supplied to that descent.
Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-ordinary-model-representative-equation). -/
theorem finiteScalarTensorRealizationForOrdinaryModels_representative
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
        (SheafOfModules.monoidalCategory Rₛ))
    (X Z : CochainComplex (Sheaf (ProEt.topology T) B) ℤ)
    (hx : P X) (hz : P Z) :
    letI := SheafOfModules.monoidalCategory Rₛ
    LF.map ((finiteScalarFixedTensorRepresentativeForCoefficients B T P hP).hom.app
        (⟨X, hx⟩, ⟨Z, hz⟩)) ≫
      ((finiteScalarTensorRealizationForOrdinaryModels B T Rₛ F LF eps P hP hF ff a b).hom.app
        (DerivedCategory.Q.obj X)).app (DerivedCategory.Q.obj Z) ≫
      a.tensor.map (Prod.mkHom (eps.hom.app X) (eps.hom.app Z)) =
    eps.hom.app (CochainComplex.mapBifunctor X Z
      (curriedTensor (Sheaf (ProEt.topology T) B))) ≫
      DerivedCategory.Q.map ((finiteScalarTotalTensorIsoOfOrdinary F b).hom.app (X, Z)) ≫
      a.representative.hom.app
        (⟨(F.mapHomologicalComplex (.up ℤ)).obj X, hF X hx⟩,
         ⟨(F.mapHomologicalComplex (.up ℤ)).obj Z, hF Z hz⟩) := by
  unfold finiteScalarTensorRealizationForOrdinaryModels
    finiteScalarTensorRealizationForModels finiteScalarTensorRealizationForCoefficients
  exact finiteScalarTensorRealizationOfRepresentatives_fac
    DerivedCategory.Q DerivedCategory.Q (F.mapHomologicalComplex (.up ℤ)) LF eps P
    (proEtaleFlatRepresentatives T Rₛ) hF ff _ _ _ a.tensor
    (finiteScalarFixedTensorRepresentativeForCoefficients B T P hP)
    a.representative (finiteScalarTotalTensorIsoOfOrdinary F b) X Z hx hz

end WeilConjectures
