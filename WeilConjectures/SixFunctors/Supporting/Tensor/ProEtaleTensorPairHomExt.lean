/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! # Intrinsic tensor morphisms determined by pure sections

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sp-proetale-tensor-pair-hom-ext).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
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
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.presheafToSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
  AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage
  AlgebraicGeometry.ProEtale.lowerStar
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

/-- Intrinsic module tensor maps are determined by their values on pure sections.
Source: Stacks Tag 03EL, tensor universal property and sheafification.
(blueprint: lem-sp-proetale-tensor-pair-hom-ext).

Proof: precompose with the inverse tensor sheafification presentation, then use
the sheafification adjunction. The resulting maps are maps from the presheaf
sectionwise tensor. At each site object they are linear maps, so induction on
tensors reduces equality to zero, pure tensors, and sums. The pure-tensor case
is the hypothesis; linearity proves the other two cases. -/
theorem proEtaleTensorPair_hom_ext (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M N H : proEtaleRingModules T R}
    (a b : ((proEtaleOrdinaryTensor T R).obj M).obj N ⟶ H)
    (h : ∀ (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      a.val.app W (proEtaleTensorPair T R M N W m n) =
        b.val.app W (proEtaleTensorPair T R M N W m n)) : a = b := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change a.val.app W ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app W
    ((adj.unit.app (M.val ⊗ N.val)).app W t)) =
    b.val.app W ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app W
      ((adj.unit.app (M.val ⊗ N.val)).app W t))
  induction t using TensorProduct.induction_on with
  | zero =>
      erw [map_zero, map_zero, map_zero, map_zero]
  | tmul m n => exact h W m n
  | add t s ht hs =>
      erw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add]
      exact congrArg₂ (· + ·) ht hs

end WeilConjectures
