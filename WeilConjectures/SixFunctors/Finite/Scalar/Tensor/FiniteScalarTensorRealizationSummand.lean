/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization

/-! The coproduct summands of the scalar total realization.

Source: Stacks Tags 06YN and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-realization-summand).
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
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

universe a v b w
private theorem totalRealization_ι
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{w} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (P Q : CochainComplex C ℤ) (a b n : ℤ) (h : a + b = n) :
    F.map (CochainComplex.ιMapBifunctor P Q (curriedTensor C) a b n h) ≫
        ((finiteScalarTotalTensorIsoOfOrdinary F e).hom.app (P, Q)).f n =
      e.hom.app (P.X a, Q.X b) ≫
        CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) a b n h := by
  simp only [finiteScalarTotalTensorIsoOfOrdinary, Iso.trans_hom, NatTrans.comp_app,
    finiteScalarUncurryPostcomposeIso_hom_app, Functor.mapIso_hom,
    uncurry_map_app, asIso_hom, HomologicalComplex.mapBifunctorComparisonNatTrans_app_app,
    Category.id_comp, HomologicalComplex.mapBifunctorComparison_f]
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (finiteScalarCurryTensorIso F e).hom (.up ℤ) P Q a b n h

private theorem realizationForFunctor_ι
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (P Q : CochainComplex C ℤ) (a b n : ℤ) (h : a + b = n) :
    F.map (CochainComplex.ιMapBifunctor P Q (curriedTensor C) a b n h) ≫
        ((finiteScalarRepresentativeTotalRealizationForFunctor F e).app (P, Q)).f n =
      e.hom.app (P.X a, Q.X b) ≫
        CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) a b n h := by
  rw [finiteScalarRepresentativeTotalRealizationForFunctor_app]
  exact totalRealization_ι F e P Q a b n h

/-- On every coproduct summand, total realization is the ordinary tensor comparison.
Source: Stacks Tags 06YN and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-realization-summand).

Proof: express realization as the total mapBifunctor comparison of its ordinary
comparison. Its defining colimit map has the stated value on each coproduct injection. -/
theorem finiteScalarRepresentativeTotalRealization_ι (R : Type u) [CommRing R] [Finite R]
    (T : Scheme.{u})
    (P Q : CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (sfIntrinsicModuleEquivalence T R).functor.map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h) ≫
      ((finiteScalarRepresentativeTotalRealization R T).app (P, Q)).f n =
    (finiteScalarOrdinaryTensorIso T R).hom.app (P.X a, Q.X b) ≫
      CochainComplex.ιMapBifunctor
        (((sfIntrinsicModuleEquivalence T R).functor.mapHomologicalComplex (.up ℤ)).obj P)
        (((sfIntrinsicModuleEquivalence T R).functor.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor _) a b n h := by
  unfold finiteScalarRepresentativeTotalRealization
  exact realizationForFunctor_ι (sfIntrinsicModuleEquivalence T R).functor
    (finiteScalarOrdinaryTensorIso T R) P Q a b n h

end WeilConjectures
