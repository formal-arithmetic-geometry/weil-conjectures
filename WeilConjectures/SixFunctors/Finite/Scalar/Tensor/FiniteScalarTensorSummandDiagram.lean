/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeChainDiagram

/-! A typed diagram for scalar total tensor comparisons.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-summand-diagram).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
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

/-- A three-stage total tensor path and its ordinary summand path.
Source: Stacks Tag 07A4, constituents of the total tensor comparison.
(blueprint: def-sf-finite-scalar-tensor-summand-diagram). -/
structure FiniteScalarTensorSummandDiagram (D : Type a) [Category.{v} D] where
  x0 : D
  x1 : D
  x2 : D
  x3 : D
  s0 : D
  s1 : D
  s2 : D
  s3 : D
  l1 : x0 ⟶ x1
  l2 : x1 ⟶ x2
  l3 : x2 ⟶ x3
  a1 : s0 ⟶ s1
  a2 : s1 ⟶ s2
  a3 : s2 ⟶ s3
  j0 : s0 ⟶ x0
  j1 : s1 ⟶ x1
  j2 : s2 ⟶ x2
  j3 : s3 ⟶ x3
  right : x0 ⟶ x3
  ordinaryRight : s0 ⟶ s3

/-- The actual scalar comparison diagram, retaining all native maps.
Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-summand-diagram).
The structure only names existing objects and maps; it asserts no compatibility. -/
def finiteScalarTensorSummandDiagram
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    FiniteScalarTensorSummandDiagram (proEtaleRingModules X (proEtaleConstantRing X R)) := by
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
  let T := proEtaleOrdinaryTensor X (proEtaleConstantRing X R)
  let G := finiteScalarTensorNativeChainDiagram R p P Q
  exact {
    x0 := (G.x0).X n
    x1 := (G.x1).X n
    x2 := (G.x2).X n
    x3 := (G.x3).X n
    s0 := V.obj (A.obj (P.X a ⊗ Q.X b))
    s1 := V.obj (AP.X a ⊗ AQ.X b)
    s2 := (T.obj (VAP.X a)).obj (VAQ.X b)
    s3 := (T.obj (BUP.X a)).obj (BUQ.X b)
    l1 := (G.l1).f n
    l2 := (G.l2).f n
    l3 := (G.l3).f n
    a1 := V.map (Functor.OplaxMonoidal.δ A (P.X a) (Q.X b))
    a2 := (finiteScalarOrdinaryTensorIso X R).hom.app (A.obj (P.X a), A.obj (Q.X b))
    a3 := (uncurry.obj T).map
      (Prod.mkHom ((finiteScalarOrdinaryPullbackComparison R p).inv.app (P.X a))
        ((finiteScalarOrdinaryPullbackComparison R p).inv.app (Q.X b)))
    j0 := (A ⋙ V).map (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h)
    j1 := V.map (CochainComplex.ιMapBifunctor AP AQ (curriedTensor _) a b n h)
    j2 := CochainComplex.ιMapBifunctor VAP VAQ T a b n h
    j3 := CochainComplex.ιMapBifunctor BUP BUQ T a b n h
    right := (G.right).f n
    ordinaryRight := (finiteScalarOrdinaryPullbackComparison R p).inv.app (P.X a ⊗ Q.X b) ≫
      B.map ((finiteScalarOrdinaryTensorIso Y R).hom.app (P.X a, Q.X b)) ≫
      (proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
        (U.obj (P.X a)) (U.obj (Q.X b))).hom }

end WeilConjectures
