/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeLeftPaths
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeRightPath

/-! The native scalar tensor diagram before taking degree components.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-native-chain-diagram).
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

/-- A three-edge path and a second map between its endpoints.
Source: Stacks Tag 07A4, total tensor comparison constituents.
(blueprint: def-sf-finite-scalar-tensor-native-chain-diagram). -/
structure FiniteScalarTensorChainDiagram (C : Type a) [Category.{v} C] where
  x0 : C
  x1 : C
  x2 : C
  x3 : C
  l1 : x0 ⟶ x1
  l2 : x1 ⟶ x2
  l3 : x2 ⟶ x3
  right : x0 ⟶ x3

/-- Assemble the actual native chain maps at the level of whole complexes.
Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-native-chain-diagram).
All vertices and arrows are the existing specified tensor and pullback data. -/
def finiteScalarTensorNativeChainDiagram
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    FiniteScalarTensorChainDiagram
      (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X R)) ℤ) := by
  let A := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let V := (sfIntrinsicModuleEquivalence X R).functor
  let U := (sfIntrinsicModuleEquivalence Y R).functor
  let B := proEtaleRingModulePullback p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let AP := (A.mapHomologicalComplex (.up ℤ)).obj P
  let AQ := (A.mapHomologicalComplex (.up ℤ)).obj Q
  let UP := (U.mapHomologicalComplex (.up ℤ)).obj P
  let UQ := (U.mapHomologicalComplex (.up ℤ)).obj Q
  let VAP := (V.mapHomologicalComplex (.up ℤ)).obj AP
  let VAQ := (V.mapHomologicalComplex (.up ℤ)).obj AQ
  let BUP := (B.mapHomologicalComplex (.up ℤ)).obj UP
  let BUQ := (B.mapHomologicalComplex (.up ℤ)).obj UQ
  let T := uncurry.obj
    ((proEtaleOrdinaryTensor X (proEtaleConstantRing X R)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
  let L := finiteScalarTensorNativeLeftPaths R p P Q
  exact {
    x0 := (V.mapHomologicalComplex (.up ℤ)).obj
      ((A.mapHomologicalComplex (.up ℤ)).obj
        ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj (P, Q)))
    x1 := (V.mapHomologicalComplex (.up ℤ)).obj
      ((finiteScalarRepresentativeTotalTensor
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj (AP, AQ))
    x2 := T.obj (VAP, VAQ)
    x3 := T.obj (BUP, BUQ)
    l1 := L.1
    l2 := L.2.1
    l3 := L.2.2
    right := finiteScalarTensorNativeRightPath R p P Q }

end WeilConjectures
