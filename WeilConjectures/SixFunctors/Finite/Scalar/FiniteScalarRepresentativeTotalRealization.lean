/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalTensor

/-! # The specified realization on shared signed total functors

Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-total-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
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

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- Assemble the existing ordinary tensor realization by its total components.
Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-total-realization). -/
@[irreducible] def finiteScalarRepresentativeTotalRealizationForFunctor
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (L : C ⥤ D) [L.Additive] [L.IsEquivalence]
    (o : tensor C ⋙ L ≅ (L.prod L) ⋙ tensor D) :
    finiteScalarRepresentativeTotalTensor C ⋙ L.mapHomologicalComplex (.up ℤ) ⟶
      ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        uncurry.obj ((curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) where
  app Z := (finiteScalarTotalTensorIsoOfOrdinary L o).hom.app Z
  naturality {_Z _W} f := (finiteScalarTotalTensorIsoOfOrdinary L o).hom.naturality f

/-- The shared realization retains the published ordinary total component.
Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-total-realization). -/
theorem finiteScalarRepresentativeTotalRealizationForFunctor_app
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [Limits.HasColimitsOfSize.{0, 0} C] [Limits.HasColimitsOfSize.{0, 0} D]
    (L : C ⥤ D) [L.Additive] [L.IsEquivalence]
    (o : tensor C ⋙ L ≅ (L.prod L) ⋙ tensor D)
    (P Q : CochainComplex C ℤ) :
    (finiteScalarRepresentativeTotalRealizationForFunctor L o).app (P, Q) =
      (finiteScalarTotalTensorIsoOfOrdinary L o).hom.app (P, Q) := by
  unfold finiteScalarRepresentativeTotalRealizationForFunctor
  rfl

/-- The shared ordinary comparison for the actual scalar realization.
Source: Stacks Tags 06YN and 07A4.
(blueprint: def-sf-finite-scalar-representative-total-realization). -/
@[irreducible] def finiteScalarRepresentativeTotalRealization
    (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u}) :=
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T R)
  finiteScalarRepresentativeTotalRealizationForFunctor
    (sfIntrinsicModuleEquivalence T R).functor (finiteScalarOrdinaryTensorIso T R)

end WeilConjectures
