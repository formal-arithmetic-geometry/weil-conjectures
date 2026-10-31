/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarComplexTensorPullback
import WeilConjectures.SixFunctors.Finite.Scalar.Fixed.FiniteScalarFixedTensorSummand

/-! The fixed-pullback injection identity mapped through scalar realization.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-mapped-fixed-summand).
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
open CategoryTheory.Limits

section
variable {C D : Type*} [Category C] [Category D]
private theorem map_formula (V : C ⥤ D) {x y z a : C}
    (j : x ⟶ y) (t : y ⟶ z) (q : x ⟶ a) (k : a ⟶ z)
    (h : j ≫ t = q ≫ k) : V.map j ≫ V.map t = V.map q ≫ V.map k := by
  rw [← V.map_comp, h, V.map_comp]
end

/-- Mapping the fixed-coefficient tensor pullback summand formula through realization.
Source: Stacks Tag 07A4, functoriality of the fixed total comparison.
(blueprint: lem-sf-finite-scalar-tensor-mapped-fixed-summand).

Proof: the fixed pullback summand formula is an equality of two composites. Apply scalar
realization's map to that equality, and use preservation of composition on both sides. -/
theorem finiteScalarTensorPullback_mapped_fixed_summand
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) ⋙
      (sfIntrinsicModuleEquivalence X R).functor).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h) ≫
    (sfIntrinsicModuleEquivalence X R).functor.map
      (((finiteScalarFixedComplexTensorPullbackForCoefficients
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).app (P, Q)).f n) =
    (sfIntrinsicModuleEquivalence X R).functor.map
        (Functor.OplaxMonoidal.δ
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) (P.X a) (Q.X b)) ≫
    (sfIntrinsicModuleEquivalence X R).functor.map
      (CochainComplex.ιMapBifunctor
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P)
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj Q)
        (curriedTensor _) a b n h) := by
  exact map_formula (sfIntrinsicModuleEquivalence X R).functor _ _ _ _
    (finiteScalarFixedComplexTensorPullback_ι R p P Q a b n h)

end WeilConjectures
