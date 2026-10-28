/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionData

/-!
# Private section and fixed-coefficient calculations for open restriction

Source: Stacks Project, Tags 03DI and 03CY; derived.tex, Tag 015F; categories.tex,
Tag 04VG (blueprint: lem-sf-open-extension-scalar-restriction-coherence).

The comparisons are the published `sfOpenRestriction` and its exact termwise
localization. Normalization is expressed on the open adjunction unit: on each
nonzero summand of the defining extension presheaf it is the identity; maps from
all remaining values, which are zero, are unique. Thus this unit equation is
precisely the pre-sheafification normalization, without a choice of stalks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme


variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

private theorem mate_whisker_top
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {G G' : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a b (w.whiskerTop t) = (mateEquiv a b w).whiskerRight t := by
  ext d : 1
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerRight,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.id_comp,
    Category.assoc]
  rw [← b.unit_naturality_assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, TwoSquare.mk, TwoSquare.natTrans]
  simp only [Category.id_comp]

-- Avoid unfolding the sheafification construction when using the adjunction API.
attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction

omit [Finite A] [Finite B] in
private theorem fixed_normalized {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B)
    (M : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
        ((sfFixedRestriction U φ).obj M) ≫
      (ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
        ((sfFixedOpenRestriction j φ).hom.app M) =
    (sfFixedRestriction U φ).map
      ((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app M) := by
  let φ' : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := φ.ulift
  let : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ').IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ').isRightAdjoint
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology U) φ').comp
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).comp
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) φ')) M
  simp only [Adjunction.comp_unit_app] at h
  let f := (ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app
      ((sfFixedRestriction U φ).obj M) ≫
    (ProEtale.openImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
      ((sfFixedOpenRestriction j φ).hom.app M)
  let g := (ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).unit.app M
  change (Sheaf.restrictCoextendScalarsAdj (ProEt.topology U) φ').unit.app M ≫
    (sheafCompose (ProEt.topology U) (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ')).map f =
    g ≫ (ProEtale.openImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map
      ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) φ').unit.app _) at h
  ext V x
  have hv := congrArg (fun k : M ⟶ _ ↦ k.hom.app V) h
  have hx := ConcreteCategory.congr_hom hv (show M.obj.obj V from x)
  have hx' := congrArg (fun z ↦ ModuleCat.CoextendScalars.equiv φ' _ z
    (1 : ULift.{u + 1, u} B)) hx
  change (f.hom.app V) ((1 : ULift.{u + 1, u} B) • (show M.obj.obj V from x)) =
    (1 : ULift.{u + 1, u} B) • (g.hom.app V x) at hx'
  change (f.hom.app V) x = (g.hom.app V) x
  simpa only [one_smul] using hx'

private theorem fixed_id_hom (T : Scheme.{u}) (R : Type u) [CommRing R]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) :
    (sfOpenFixedRestrictionId T R).hom.app M = 𝟙 M := by
  rfl

private theorem realization_apply (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (V : T.ProEtᵒᵖ) (x : ((sfIntrinsicModuleEquivalence T B).functor.obj M).val.obj V) :
    ((sfRealizationRestriction T φ).hom.app M).val.app V x = x :=
  (sfRealizationRestriction_existsUnique T φ).exists.choose_spec M V x

omit [Finite A] [Finite B] [Finite C] in
private theorem restriction_comp_apply (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C))
    (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    ((sfCoefficientRestrictionComp T φ ψ).hom.app M).val.app V x = x := by
  exact (pbcRestrictComp_exists _ _ _
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp
      (CommRingCat.ofHom φ.ulift) (CommRingCat.ofHom ψ.ulift)).symm).exists.choose_spec M V x

/-- The normalized realization comparisons compose on every section.
Source: Stacks Tags 00YV and 03DA.
Proof: realization and the coefficient compositor preserve each section, so
evaluating the two composites at an arbitrary section makes them identical.
(blueprint: lem-sf-open-scalar-realization-calculations). -/
private theorem realization_comp (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (proEtaleCoefficientRestrictScalars T φ).map
        ((sfRealizationRestriction T ψ).hom.app M) ≫
      (sfRealizationRestriction T φ).hom.app ((sfFixedRestriction T ψ).obj M) =
    (sfCoefficientRestrictionComp T φ ψ).hom.app
        ((sfIntrinsicModuleEquivalence T C).functor.obj M) ≫
      (sfRealizationRestriction T (ψ.comp φ)).hom.app M := by
  ext V x
  change ((sfRealizationRestriction T φ).hom.app ((sfFixedRestriction T ψ).obj M)).val.app
      V (((sfRealizationRestriction T ψ).hom.app M).val.app V x) =
    ((sfRealizationRestriction T (ψ.comp φ)).hom.app M).val.app V
      (((sfCoefficientRestrictionComp T φ ψ).hom.app
        ((sfIntrinsicModuleEquivalence T C).functor.obj M)).val.app V x)
  rw [realization_apply, realization_apply, restriction_comp_apply, realization_apply]

private theorem coefficient_id_apply (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R]
    (M : proEtaleRingModules T (proEtaleConstantRing T R))
    (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    ((sfOpenCoefficientRestrictionId T R).hom.app M).val.app V x = x := by
  simp only [sfOpenCoefficientRestrictionId, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, fixed_id_hom,
    ]
  erw [(sfIntrinsicModuleEquivalence T R).functor.map_id]
  change ((sfIntrinsicModuleEquivalence T R).counitIso.hom.app M).val.app V
    (((sfRealizationRestriction T (RingHom.id R)).hom.app
      ((sfIntrinsicModuleEquivalence T R).inverse.obj M)).val.app V
      (((sfIntrinsicModuleEquivalence T R).counitIso.inv.app M).val.app V x)) = x
  rw [realization_apply]
  exact congrArg (fun f : M ⟶ M ↦ f.val.app V x)
    ((sfIntrinsicModuleEquivalence T R).counitIso.inv_hom_id_app M)

private theorem restriction_id_comp (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R]
    (M : proEtaleRingModules T (proEtaleConstantRing T R)) :
    (sfCoefficientRestrictionComp T (RingHom.id R) (RingHom.id R)).hom.app M =
      (proEtaleCoefficientRestrictScalars T (RingHom.id R)).map
        ((sfOpenCoefficientRestrictionId T R).hom.app M) := by
  ext V x
  change ((sfCoefficientRestrictionComp T (RingHom.id R) (RingHom.id R)).hom.app M).val.app
    V x = ((sfOpenCoefficientRestrictionId T R).hom.app M).val.app V x
  rw [restriction_comp_apply, coefficient_id_apply]

-- The remaining argument uses only the equivalence and its unit/counit API.

end AlgebraicGeometry.Scheme
