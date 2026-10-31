/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! # Fixed-coefficient pullback tensorator on pure unit sections

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pullback-fixed-pure).
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

private def fixedPair (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
  (Functor.LaxMonoidal.μ
    (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) M N).app W
      (m ⊗ₜ[ULift.{u + 1} R] n)

private theorem fixedPair_map (T : Scheme.{u}) (R : Type u) [CommRing R]
    {M M' N N' : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))}
    (f : M ⟶ M') (g : N ⟶ N') (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) :
    (f ⊗ₘ g).hom.app W (fixedPair T R M N W m n) =
      fixedPair T R M' N' W (f.hom.app W m) (g.hom.app W n) := by
  exact (congrArg (fun z ↦ z.app W (m ⊗ₜ[ULift.{u + 1} R] n))
    (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
      f g)).symm

private theorem fixedPush_tensor (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
    Functor.LaxMonoidal.μ
        (sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M)
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj N) ≫
      (Functor.LaxMonoidal.μ
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) M N).hom =
      Functor.whiskerLeft (proEtaleBaseChange p).op
        (Functor.LaxMonoidal.μ
          (sheafToPresheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
          M N) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} R)
  let b := proEtaleBaseChange p
  let i := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    b B (ProEt.topology Y) (ProEt.topology X)
  have hi (P : Sheaf (ProEt.topology X) B) : i.hom.app P = 𝟙 _ := by
    change (sheafificationAdjunction (ProEt.topology Y) B).unit.app
      ((sheafToPresheaf (ProEt.topology Y) B).obj
        ((ProEtale.lowerStar B p).obj P)) ≫
      (sheafToPresheaf (ProEt.topology Y) B).map
        ((sheafificationAdjunction (ProEt.topology Y) B).counit.app
          ((ProEtale.lowerStar B p).obj P)) = _
    exact (sheafificationAdjunction (ProEt.topology Y) B).right_triangle_components _
  have ht := NatTrans.IsMonoidal.tensor (τ := i.hom) M N
  erw [Functor.LaxMonoidal.comp_μ, hi, hi, hi] at ht
  erw [tensorHom_id, Category.id_comp, Category.comp_id] at ht
  erw [MonoidalCategory.id_whiskerRight, Category.id_comp] at ht
  exact ht.symm

/-- The fixed-coefficient inverse-image tensorator preserves pure unit sections.
Source: Stacks Tag 03EL, tensor product and inverse image.
(blueprint: lem-sf-finite-scalar-tensor-pullback-fixed-pure).

Proof: the fixed-coefficient pullback adjunction is monoidal. Its unit tensor
identity describes the oplax tensorator as the transpose of tensoring the two
units. Naturality of the forgetful tensorator moves the two units through a pure
pair. The right-adjoint monoidal structure is sectionwise restriction, so its
pure pair at an object is the pair at the base-changed object. Combining these
identities gives the claimed section formula. -/
theorem finiteScalarTensorPullback_fixed_pure (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : Y.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) :
    let pair (T : Scheme.{u}) (R : Type u) [CommRing R]
        (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
        (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
      (Functor.LaxMonoidal.μ
        (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) M N).app W
          (m ⊗ₜ[ULift.{u + 1} R] n)
    (Functor.OplaxMonoidal.δ
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) M N).hom.app
        ((proEtaleBaseChange p).op.obj W)
      (((ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).unit.app (M ⊗ N)).hom.app W
          (pair Y R M N W m n)) =
      pair X R
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M)
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj N)
        ((proEtaleBaseChange p).op.obj W)
        (((ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).unit.app M).hom.app W m)
        (((ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).unit.app N).hom.app W n) := by
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  have : a.IsMonoidal := inferInstanceAs
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (proEtaleBaseChange p) (ModuleCat.{u + 1} (ULift.{u + 1} R))
      (ProEt.topology Y) (ProEt.topology X)).IsMonoidal)
  have h := congrArg (fun z ↦ z.hom.app W (fixedPair Y R M N W m n))
    (a.unit_app_tensor_comp_map_δ M N)
  change _ = (Functor.LaxMonoidal.μ
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) _ _).hom.app W
      ((a.unit.app M ⊗ₘ a.unit.app N).hom.app W (fixedPair Y R M N W m n)) at h
  have hmap := fixedPair_map Y R (a.unit.app M) (a.unit.app N) W m n
  have h' := h.trans (congrArg (fun z ↦ (Functor.LaxMonoidal.μ
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) _ _).hom.app W z) hmap)
  have hh := congrArg (fun z ↦ z.app W
    (((a.unit.app M).hom.app W m) ⊗ₜ[ULift.{u + 1} R]
      ((a.unit.app N).hom.app W n)))
    (fixedPush_tensor R p
      ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M)
      ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj N))
  exact h'.trans hh

end WeilConjectures
