/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! # Scalar tensor realization on pure scalar-unit sections

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sf-finite-scalar-tensor-realization-pure).
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

private def fixedTensorPresentation (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
    (presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))).obj
      (M.obj ⊗ N.obj) ≅ M ⊗ N :=
  let U := sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let L := presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let c := asIso (sheafificationAdjunction (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} R))).counit
  (isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
    isoWhiskerRight (NatIso.prod c c) (tensor _)).app (M, N)

private theorem fixedTensorPresentation_unit (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
    toSheafify (ProEt.topology T) (M.obj ⊗ N.obj) ≫
        (fixedTensorPresentation T R M N).hom.hom =
      Functor.LaxMonoidal.μ
        (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) M N := by
  rfl

private def fixedPair (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
  (Functor.LaxMonoidal.μ
    (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) M N).app W
      (m ⊗ₜ[ULift.{u + 1} R] n)

private theorem tensorPresentation_cancel
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {Z H : D} (e : X ≅ Y) (q : Z ≅ F.obj X) (h : Z ⟶ H) :
    q.hom ≫ F.map e.hom ≫ F.map e.inv ≫ q.inv ≫ h = h := by
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp,
    Iso.hom_inv_id_assoc]

/-- Scalar tensor realization carries pure scalar-unit sections to intrinsic pure pairs.
Source: Stacks Tags 00YV and 03EL, module realization and sheafification of tensors.
(blueprint: lem-sf-finite-scalar-tensor-realization-pure).

Proof: express the fixed tensor as sheafification of its presheaf tensor. The
forgetful lax tensorator is its sheafification unit followed by this presentation.
In the specified realization tensor comparison, the presentation and the realized
fixed sheafification unit cancel with their inverses. The remaining map is the
intrinsic sheafification tensor comparison. Its pure-section normalization and
naturality of the scalar sheafification unit give precisely the displayed formula. -/
theorem finiteScalarTensorRealization_pure (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) :
    let pair (T : Scheme.{u}) (R : Type u) [CommRing R]
        (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
        (W : T.ProEtᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
      (Functor.LaxMonoidal.μ
        (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) M N).app W
          (m ⊗ₜ[ULift.{u + 1} R] n)
    ((finiteScalarOrdinaryTensorIso T R).hom.app (M, N)).val.app W
        (sfIntrinsicRealizationUnit T R (M ⊗ N) W (pair T R M N W m n)) =
      proEtaleTensorPair T (proEtaleConstantRing T R)
        ((sfIntrinsicModuleEquivalence T R).functor.obj M)
        ((sfIntrinsicModuleEquivalence T R).functor.obj N) W
        (sfIntrinsicRealizationUnit T R M W m) (sfIntrinsicRealizationUnit T R N W n) := by
  change ((finiteScalarOrdinaryTensorIso T R).hom.app (M, N)).val.app W
        (sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n)) =
      proEtaleTensorPair T (proEtaleConstantRing T R)
        ((sfIntrinsicModuleEquivalence T R).functor.obj M)
        ((sfIntrinsicModuleEquivalence T R).functor.obj N) W
        (sfIntrinsicRealizationUnit T R M W m) (sfIntrinsicRealizationUnit T R N W n)
  let J := ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1} R)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)
  let S := PresheafOfModules.sheafification.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R)
  let F := (sfIntrinsicModuleEquivalence T R).functor
  let P := M.obj ⊗ N.obj
  let eS := Classical.choose
    (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
      (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R))
  have he : S.map (E.map (toSheafify J P)) ≫ F.map
        (fixedTensorPresentation T R M N).hom ≫
        (finiteScalarOrdinaryTensorIso T R).hom.app (M, N) =
      eS.inv.app (E.obj M.obj, E.obj N.obj) := by
    have : IsIso (S.map (E.map (toSheafify J P))) :=
      finiteScalarModuleSheafificationUnit_isIso T R P
    let t : E ⋙ S ⟶ presheafToSheaf J B ⋙ F :=
      Functor.whiskerRight (sheafificationAdjunction J B).unit (E ⋙ S)
    have : IsIso t := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Q
      exact finiteScalarModuleSheafificationUnit_isIso T R Q
    have hid : S.map (𝟙 (E.obj P)) ≫ eS.inv.app (E.obj M.obj, E.obj N.obj) =
        eS.inv.app (E.obj M.obj, E.obj N.obj) := by erw [S.map_id, Category.id_comp]
    unfold finiteScalarOrdinaryTensorIso
    change ((asIso t).app P).hom ≫
      F.map (fixedTensorPresentation T R M N).hom ≫
      F.map (fixedTensorPresentation T R M N).inv ≫ ((asIso t).app P).inv ≫
        (S.map (𝟙 _) ≫ eS.inv.app (E.obj M.obj, E.obj N.obj)) = _
    exact (tensorPresentation_cancel F (fixedTensorPresentation T R M N)
      ((asIso t).app P) _).trans hid
  have hη := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R)).unit.naturality
      (E.map (toSheafify J P ≫ (fixedTensorPresentation T R M N).hom.hom))
  have hp := congrArg (fun z ↦ z.app W (m ⊗ₜ[ULift.{u + 1} R] n)) hη
  have hh := congrArg (fun z ↦ z.val.app W
    (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R)).unit.app (E.obj P)).app W
        (m ⊗ₜ[ULift.{u + 1} R] n))) he
  have hs := Classical.choose_spec
    (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
      (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R))
  rw [fixedTensorPresentation_unit] at hp
  change sfIntrinsicRealizationUnit T R (M ⊗ N) W (fixedPair T R M N W m n) = _ at hp
  rw [hp]
  have hm : S.map (E.map (Functor.LaxMonoidal.μ
      (sheafToPresheaf J B) M N)) =
      S.map (E.map (toSheafify J P)) ≫ F.map
        (fixedTensorPresentation T R M N).hom := by
    rw [← fixedTensorPresentation_unit T R M N, E.map_comp, S.map_comp]
    rfl
  change ((finiteScalarOrdinaryTensorIso T R).hom.app (M, N)).val.app W
    ((S.map (E.map (Functor.LaxMonoidal.μ (sheafToPresheaf J B) M N))).val.app W _) = _
  rw [hm]
  have ht := hh.trans (hs (E.obj M.obj) (E.obj N.obj) W m n)
  change ((finiteScalarOrdinaryTensorIso T R).hom.app (M, N)).val.app W
    ((F.map (fixedTensorPresentation T R M N).hom).val.app W
      ((S.map (E.map (toSheafify J P))).val.app W _)) = _
  exact ht

end WeilConjectures
