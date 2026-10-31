/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! The tensor map of the termwise scalar comparison on a summand.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-comparison-map-summand).
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

universe a v
open CategoryTheory.Limits

private theorem totalTensor_map {C : Type a} [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{0} C]
    {Z W : CochainComplex C ℤ × CochainComplex C ℤ} (f : Z ⟶ W) :
    (uncurry.obj ((curriedTensor C).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).map f =
      HomologicalComplex.mapBifunctorMap f.1 f.2 (curriedTensor C) (.up ℤ) := by
  simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex]
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

private theorem comparison_f (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) (n : ℤ) :
    ((finiteScalarComplexPullbackComparison R p).inv.app P).f n =
      (finiteScalarOrdinaryPullbackComparison R p).inv.app (P.X n) := by
  simpa only [finiteScalarComplexPullbackComparison] using
    Functor.mapHomologicalComplexCompIso_inv_app_f
      (finiteScalarOrdinaryPullbackComparison R p) (.up ℤ) P n

/-- The total tensor of the termwise scalar comparison has its ordinary tensor on summands.
Source: Stacks Tag 07A4; Mathlib's `HomologicalComplex.ι_mapBifunctorMap`.
(blueprint: lem-sf-finite-scalar-tensor-comparison-map-summand).

Proof: expand the uncurried total tensor map as mapBifunctorMap. Its injection formula
is the tensor of the two degree components followed by the target injection. The complex
scalar comparison has the ordinary scalar comparison in each degree, by the component
formula for mapHomologicalComplexCompIso. Expand the ordinary uncurried tensor map and
reassociate; the two expressions are definitionally equal. -/
theorem finiteScalarTensorPullback_comparison_map_summand
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    CochainComplex.ιMapBifunctor
      (((sfIntrinsicModuleEquivalence X R).functor.mapHomologicalComplex (.up ℤ)).obj
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P))
      (((sfIntrinsicModuleEquivalence X R).functor.mapHomologicalComplex (.up ℤ)).obj
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj Q))
      (proEtaleOrdinaryTensor X (proEtaleConstantRing X R)) a b n h ≫
      (((uncurry.obj
        ((proEtaleOrdinaryTensor X (proEtaleConstantRing X R)).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ))).map
            (Prod.mkHom ((finiteScalarComplexPullbackComparison R p).inv.app P)
              ((finiteScalarComplexPullbackComparison R p).inv.app Q))).f n) =
    ((uncurry.obj (proEtaleOrdinaryTensor X (proEtaleConstantRing X R))).map
      (Prod.mkHom ((finiteScalarOrdinaryPullbackComparison R p).inv.app (P.X a))
        ((finiteScalarOrdinaryPullbackComparison R p).inv.app (Q.X b)))) ≫
    CochainComplex.ιMapBifunctor
      (((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
        (.up ℤ)).obj (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj P))
      (((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
        (.up ℤ)).obj (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj Q)) (proEtaleOrdinaryTensor X (proEtaleConstantRing X R)) a b n h := by
  rw [totalTensor_map, HomologicalComplex.ι_mapBifunctorMap]
  simp only [comparison_f, proEtaleOrdinaryTensor, Functor.uncurry_obj_map,
    curriedTensor_obj_map, curriedTensor_map_app, Functor.comp_obj,
    curriedTensor_obj_obj, Category.assoc]
  rfl

end WeilConjectures
