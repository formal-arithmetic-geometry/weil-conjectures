/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! # Naturality of the intrinsic pure tensor pairing

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sp-proetale-tensor-pair-naturality).
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

set_option maxHeartbeats 600000 in
-- Compare the monoidal sheafification presentation with its counit formula.
private theorem intrinsicTensorIso_natural (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M M' N N' : proEtaleRingModules T R} (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory R
    (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let ε := asIso adj.counit
  have hf := ε.inv.naturality f
  have hg := ε.inv.naturality g
  change f ≫ ε.inv.app M' =
    ε.inv.app M ≫ (PresheafOfModules.sheafification (𝟙 _)).map f.val at hf
  change g ≫ ε.inv.app N' =
    ε.inv.app N ≫ (PresheafOfModules.sheafification (𝟙 _)).map g.val at hg
  unfold SheafOfModules.tensorObjIsoSheafification
  change (f ⊗ₘ g) ≫ (ε.inv.app M' ⊗ₘ ε.inv.app N') ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 _)) M'.val N'.val =
    (ε.inv.app M ⊗ₘ ε.inv.app N) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 _)) M.val N.val ≫
      (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val)
  erw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural]
  rfl

/-- The intrinsic pure tensor pairing is natural in both module arguments.
Source: Stacks Tag 03EL, the sheafified sectionwise tensor product.
(blueprint: lem-sp-proetale-tensor-pair-naturality).

Proof: the tensor presentation is formed from the inverse sheafification counits
and the sheafification tensorator. Naturality of the counits and of the lax
monoidal tensorator proves its naturality. Move the presentation across that
identity using its inverse, then evaluate naturality of the sheafification unit
on a pure tensor. Their composite is exactly the asserted pure-pair identity. -/
theorem proEtaleTensorPair_natural (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M M' N N' : proEtaleRingModules T R} (f : M ⟶ M') (g : N ⟶ N')
    (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    letI := SheafOfModules.monoidalCategory R
    (f ⊗ₘ g).val.app W (proEtaleTensorPair T R M N W m n) =
      proEtaleTensorPair T R M' N' W (f.val.app W m) (g.val.app W n) := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  have h : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← intrinsicTensorIso_natural T R f g,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn := adj.unit.naturality (f.val ⊗ₘ g.val)
  have hh := congrArg (fun z ↦ z.val.app W
    ((adj.unit.app (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))) h
  have hu := congrArg (fun z ↦ z.app W (m ⊗ₜ[R.obj.obj W] n)) hn.symm
  change ((PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val)).val.app W
      ((adj.unit.app (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n)) = _ at hu
  change (f ⊗ₘ g).val.app W (proEtaleTensorPair T R M N W m n) =
    (SheafOfModules.tensorObjIsoSheafification M' N').inv.val.app W _ at hh
  exact hh.trans (congrArg
    ((SheafOfModules.tensorObjIsoSheafification M' N').inv.val.app W) hu)

end WeilConjectures
