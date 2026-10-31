/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeLeftPaths
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeRightPath
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeChainDiagram
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeChainCommutes

/-! The named native scalar tensor paths are equal.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-native-paths-equal).
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
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

universe a v
open CategoryTheory.Limits

attribute [local implicit_reducible] finiteScalarTensorNativeChainDiagram
attribute [local irreducible] finiteScalarTensorNativeLeftPaths finiteScalarTensorNativeRightPath

/-- The explicit tuple's three chain maps compose to the named right native path.
Source: Stacks Tag 07A4, specified total tensor comparison constituents.
(blueprint: lem-sf-finite-scalar-tensor-native-paths-equal).

Proof: apply the proved native cochain diagram equality. Reduce its data constructor
while retaining the two named native paths. This only projects the stored arrows. -/
theorem finiteScalarTensorNative_paths_equal
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (finiteScalarTensorNativeLeftPaths R p P Q).1 ≫
      (finiteScalarTensorNativeLeftPaths R p P Q).2.1 ≫
      (finiteScalarTensorNativeLeftPaths R p P Q).2.2 =
    finiteScalarTensorNativeRightPath R p P Q := by
  exact finiteScalarTensorNativeChain_commutes R p P Q

end WeilConjectures
