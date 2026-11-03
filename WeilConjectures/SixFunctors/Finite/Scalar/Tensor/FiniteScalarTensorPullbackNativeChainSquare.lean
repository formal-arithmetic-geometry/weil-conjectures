/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarComplexTensorPullback
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativePathsEqual
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeLeftEdge1
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeLeftEdge2
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeLeftEdge3
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeRightEdge

/-! The native scalar tensor pullback chain square.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-pullback-native-chain-square).
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
attribute [local irreducible] finiteScalarTensorNativeLeftPaths finiteScalarTensorNativeRightPath

universe a v
open CategoryTheory.Limits

/-- The specified three native left chain maps compose to the specified native right path.
Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-pullback-native-chain-square).

Proof: rewrite each original native left map by its proved tuple-projection
identification, and the original right composite by its proved native-path
identification. Apply the equality of those named paths, itself proved from the native
cochain diagram. Work before degree evaluation so the native chain types can be reused. -/
theorem finiteScalarTensorPullback_native_chain_square
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    ((((sfIntrinsicModuleEquivalence X R).functor.mapHomologicalComplex (.up ℤ)).map
        ((finiteScalarFixedComplexTensorPullbackForCoefficients
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).app (P, Q))) ≫
      (finiteScalarRepresentativeTotalRealization R X).app
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P,
         ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj Q) ≫
      (uncurry.obj ((proEtaleOrdinaryTensor X (proEtaleConstantRing X R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))).map
        (Prod.mkHom ((finiteScalarComplexPullbackComparison R p).inv.app P)
          ((finiteScalarComplexPullbackComparison R p).inv.app Q))) =
    ((finiteScalarComplexPullbackComparison R p).inv.app
        ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj (P, Q)) ≫
      ((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
        (.up ℤ)).map ((finiteScalarRepresentativeTotalRealization R Y).app (P, Q)) ≫
      (finiteScalarIntrinsicComplexTensorPullback R p).app
        (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P,
         ((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj Q)) := by
  rw [finiteScalarTensorNativeLeft_edge1, finiteScalarTensorNativeLeft_edge2,
    finiteScalarTensorNativeLeft_edge3, ← finiteScalarTensorNativeRight_edge]
  exact finiteScalarTensorNative_paths_equal R p P Q

end WeilConjectures
