/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorScalarSourceModelRepresentativeEquation

/-! # Scalar tensor realization on a fixed representative

Source: Stacks Project, Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-pullback-representative-equation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 40000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
  SheafOfModules.monoidalCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  DerivedCategory.Q HasDerivedCategory.standard
  CategoryTheory.Functor.mapHomologicalComplex CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
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

/-- The normalized scalar tensor realization satisfies its representative equation on a
fixed flat-term K-flat pair. This is the Y-side substep of the scalar tensor-pullback
representative square.

Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-pullback-representative-equation).
-/
theorem finiteScalarTensorRealization_Y_representative
    (R : Type u) [CommRing R] [Finite R]
    {Y : Scheme.{u}}
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hP : finiteScalarFlatRepresentatives Y R P)
    (hQ : finiteScalarFlatRepresentatives Y R Q) :
    (sfIntrinsicDerivedEquivalence Y R).functor.map
        ((finiteScalarFixedTensorRepresentativeForCoefficients
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) Y
          (finiteScalarFlatRepresentatives Y R)
          (finiteScalarFlatRepresentatives_kFlat Y R)).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
      ((finiteScalarTensorRealization Y R aY).hom.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      aY.tensor.map (Prod.mkHom
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app P)
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app Q)) =
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app
        (CochainComplex.mapBifunctor P Q
          (curriedTensor (Sheaf (ProEt.topology Y)
            (ModuleCat.{u + 1} (ULift.{u + 1} R))))) ≫
      DerivedCategory.Q.map
        ((finiteScalarTotalTensorIso Y R).hom.app (P, Q)) ≫
      aY.representative.hom.app
        (⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj P, finiteScalarPreservesRepresentatives Y R P hP⟩,
         ⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj Q, finiteScalarPreservesRepresentatives Y R Q hQ⟩) := by
  unfold finiteScalarTensorRealization finiteScalarTotalTensorIso
  apply finiteScalarTensorRealizationForScalarSourceModels_representative R Y
    (proEtaleConstantRing Y R)

end WeilConjectures
