/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorSignedChain
import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryTensorBraiding

/-! # The realized scalar comparison preserves the signed chain swap

Source: Stacks Tags 06YL and 0FPT.
(blueprint: lem-sf-finite-scalar-mapped-realized-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

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

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures.IntegralVerdier

attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CategoryTheory.Equivalence.mapDerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- Signed totalization commutes with a further functor before coefficient specialization.
Source: Stacks 06YL and 0FPT.
Proof: specialize the generic mapped total square to scalar realization and its
ordinary pure-tensor braiding equation.
(blueprint: lem-sf-finite-scalar-mapped-realized-braiding). -/
theorem finiteScalarMappedRealizedBraiding
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    {D : Type*} [Category D]
    (q : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X B)) ℤ ⥤ D)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) ℤ) :
    let := SheafOfModules.monoidalCategory (proEtaleConstantRing X B)
    let := SheafOfModules.symmetricCategory (proEtaleConstantRing X B)
    let U := (sfIntrinsicModuleEquivalence X B).functor.mapHomologicalComplex (.up ℤ)
    q.map (U.map (totalTensorBraiding Q P).inv) ≫
        q.map ((finiteScalarTotalTensorIsoOfOrdinary
          (sfIntrinsicModuleEquivalence X B).functor
          (finiteScalarOrdinaryTensorIso X B)).hom.app (Q, P)) =
      q.map ((finiteScalarTotalTensorIsoOfOrdinary
          (sfIntrinsicModuleEquivalence X B).functor
          (finiteScalarOrdinaryTensorIso X B)).hom.app (P, Q)) ≫
        q.map (totalTensorBraiding (U.obj P) (U.obj Q)).hom := by
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing X B)
  let := SheafOfModules.symmetricCategory (proEtaleConstantRing X B)
  exact finiteScalarTensorSignedChainMapped
    (sfIntrinsicModuleEquivalence X B).functor (finiteScalarOrdinaryTensorIso X B)
    (finiteScalarOrdinaryTensorIso_braiding X B) q P Q

end WeilConjectures.IntegralVerdier
