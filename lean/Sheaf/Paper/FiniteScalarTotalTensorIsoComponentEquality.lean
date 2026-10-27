/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteScalarTensorComplex
public import Sheaf.Paper.FiniteScalarTensorResolution

/-! # Component normalization for the finite scalar total tensor comparison

Source: Stacks Project, Tags 06YN and 07A4.
(blueprint: lem-sf-finite-scalar-total-tensor-iso-component-equality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

/-- The ordinary and specialized total tensor comparisons have the same component
normalization after the intrinsic equivalence.

Proof: expand the specialized total comparison through its ordinary construction.
The component at `(P,Q)` is the signed total map transported by the intrinsic
equivalence, while the specialized notation is the same map after the local
`let` binding.  The representative map then composes with equal endpoints,
so the displayed composites coincide by the naturality and identity laws.

Source: Stacks Tags 06YN and 07A4.
(blueprint: lem-sf-finite-scalar-total-tensor-iso-component-equality).
-/
theorem finiteScalarTotalTensorIso_representative_component_eq
    (R : Type u) [CommRing R] [Finite R]
    {Y : Scheme.{u}}
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hP : finiteScalarFlatRepresentatives Y R P)
    (hQ : finiteScalarFlatRepresentatives Y R Q) :
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app
        (CochainComplex.mapBifunctor P Q
          (curriedTensor (Sheaf (ProEt.topology Y)
            (ModuleCat.{u + 1} (ULift.{u + 1} R))))) ≫
      DerivedCategory.Q.map ((finiteScalarTotalTensorIso Y R).hom.app (P, Q)) ≫
      aY.representative.hom.app
        (⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj P, finiteScalarPreservesRepresentatives Y R P hP⟩,
         ⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj Q, finiteScalarPreservesRepresentatives Y R Q hQ⟩) =
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app
        ((Functor.uncurry.obj ((curriedTensor
          (Sheaf (ProEt.topology Y)
            (ModuleCat.{u + 1} (ULift.{u + 1} R)))).map₂HomologicalComplex
              (.up ℤ) (.up ℤ) (.up ℤ))).obj (P, Q)) ≫
      DerivedCategory.Q.map
        ((finiteScalarTotalTensorIsoOfOrdinary
          (sfIntrinsicModuleEquivalence Y R).functor
          (finiteScalarOrdinaryTensorIso Y R)).hom.app (P, Q)) ≫
      aY.representative.hom.app
        (⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj P, finiteScalarPreservesRepresentatives Y R P hP⟩,
         ⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj Q, finiteScalarPreservesRepresentatives Y R Q hQ⟩) := by sorry

end WeilConjectures
