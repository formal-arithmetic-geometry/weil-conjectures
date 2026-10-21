/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Coherent scalar restriction for open extension by zero

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
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme


variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- The sectionwise coefficient square for restriction to an open, transported by
exactly the canonical realization equivalences used to define extension by zero.
Its fixed-scalar middle square is the identity: precomposition with the open site
functor commutes with restriction of scalars.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenRestrictionCoefficientSquare {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars Z φ ⋙ sfIntrinsicOpenRestriction j A ≅
      sfIntrinsicOpenRestriction j B ⋙ proEtaleCoefficientRestrictScalars U φ :=
  Functor.isoWhiskerRight (sfInverseRealizationRestriction Z φ)
      (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence U A).functor) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Z B).inverse
      (Functor.isoWhiskerRight (Iso.refl
        (sfFixedRestriction Z φ ⋙
          ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))
        (sfIntrinsicModuleEquivalence U A).functor) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence Z B).inverse ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (sfRealizationRestriction U φ).symm

/-- Identity coefficient restriction in fixed-scalar coordinates, with the identity
on every section. Source: Stacks Tag 03DA
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenFixedRestrictionId (T : Scheme.{u}) (R : Type u) [CommRing R] :
    sfFixedRestriction T (RingHom.id R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf (ProEt.topology T) _).preimageIso
      (Functor.isoWhiskerLeft M.obj
        (ModuleCat.restrictScalarsId' (RingHom.id R).ulift rfl)))
    (fun f ↦ by ext V x; rfl)

/-- The canonical identity coefficient comparison in intrinsic coordinates. It is
transported from the sectionwise identity, using the already section-normalized
realization comparison and the realization counit.
Source: Stacks Tags 03CY and 03DA
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenCoefficientRestrictionId (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] :
    proEtaleCoefficientRestrictScalars T (RingHom.id R) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T R).counitIso.symm
      (proEtaleCoefficientRestrictScalars T (RingHom.id R)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T R).inverse
      (sfRealizationRestriction T (RingHom.id R)) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T R).inverse
      (Functor.isoWhiskerRight (sfOpenFixedRestrictionId T R)
        (sfIntrinsicModuleEquivalence T R).functor) ≪≫
    (sfIntrinsicModuleEquivalence T R).counitIso

/-- The identity on the extension presheaf, expressed by its generators over the
open. The unit of the recorded adjunction is the sheafification map on those
generators. Every other presheaf value is zero, so this equation includes all its
components. The coefficient square uses only the canonical realization maps.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def SfOpenRestrictionNormalized {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B)
    (e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
      sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ) : Prop :=
  ∀ M : proEtaleRingModules U (proEtaleConstantRing U B),
    (sfIntrinsicExtensionByZeroAdjunction j A).unit.app
        ((proEtaleCoefficientRestrictScalars U φ).obj M) ≫
      (sfIntrinsicOpenRestriction j A).map (e.hom.app M) ≫
      (sfOpenRestrictionCoefficientSquare j φ).hom.app
        ((sfIntrinsicExtensionByZero j B).obj M) =
    (proEtaleCoefficientRestrictScalars U φ).map
      ((sfIntrinsicExtensionByZeroAdjunction j B).unit.app M)

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
attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem inverse_realization_mate (T : Scheme.{u}) (φ : A →+* B) :
    mateEquiv (sfIntrinsicModuleEquivalence T B).symm.toAdjunction
        (sfIntrinsicModuleEquivalence T A).symm.toAdjunction
        (TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).hom) =
      TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).hom := by
  apply (mateEquiv (sfIntrinsicModuleEquivalence T B).symm.toAdjunction
    (sfIntrinsicModuleEquivalence T A).symm.toAdjunction).symm.injective
  simp only [Equiv.symm_apply_apply]
  ext M : 1
  simp only [sfInverseRealizationRestriction, mateEquiv_symm_apply,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [Equivalence.symm, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.counit, TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  all_goals rfl

private theorem inverse_realization_comp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) :
    (sfIntrinsicModuleEquivalence T A).inverse.map
        ((sfCoefficientRestrictionComp T φ ψ).hom.app M) ≫
      (sfInverseRealizationRestriction T (ψ.comp φ)).hom.app M =
    (sfInverseRealizationRestriction T φ).hom.app
        ((proEtaleCoefficientRestrictScalars T ψ).obj M) ≫
      (sfFixedRestriction T φ).map ((sfInverseRealizationRestriction T ψ).hom.app M) := by
  have h : (TwoSquare.mk _ _ _ _
        (sfInverseRealizationRestriction T (ψ.comp φ)).hom).whiskerTop
        (sfCoefficientRestrictionComp T φ ψ).hom =
      (TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T ψ).hom) ≫ₕ
        (TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).hom) := by
    apply (mateEquiv (sfIntrinsicModuleEquivalence T C).symm.toAdjunction
      (sfIntrinsicModuleEquivalence T A).symm.toAdjunction).injective
    rw [mate_whisker_top, inverse_realization_mate]
    erw [mateEquiv_vcomp _ (sfIntrinsicModuleEquivalence T B).symm.toAdjunction,
      inverse_realization_mate, inverse_realization_mate]
    ext N : 1
    simp only [TwoSquare.whiskerRight, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    exact (realization_comp T φ ψ N).symm
  simpa only [TwoSquare.whiskerTop, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using congr_app h M

private theorem realization_inv_comp (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfRealizationRestriction T φ).inv.app ((sfFixedRestriction T ψ).obj M) ≫
      (proEtaleCoefficientRestrictScalars T φ).map
        ((sfRealizationRestriction T ψ).inv.app M) ≫
      (sfCoefficientRestrictionComp T φ ψ).hom.app
        ((sfIntrinsicModuleEquivalence T C).functor.obj M) =
    (sfRealizationRestriction T (ψ.comp φ)).inv.app M := by
  apply (cancel_epi ((sfRealizationRestriction T (ψ.comp φ)).hom.app M)).mp
  rw [← cancel_epi ((sfCoefficientRestrictionComp T φ ψ).hom.app
    ((sfIntrinsicModuleEquivalence T C).functor.obj M))]
  rw [← Category.assoc, ← realization_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem forward_realization_mate (T : Scheme.{u}) (φ : A →+* B) :
    mateEquiv (sfIntrinsicModuleEquivalence T B).toAdjunction
        (sfIntrinsicModuleEquivalence T A).toAdjunction
        (TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).inv) =
      TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).inv := by
  ext M : 1
  simp only [sfInverseRealizationRestriction, mateEquiv_apply,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp,
    Category.assoc]
  dsimp only [Equivalence.symm, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.counit, TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  all_goals rfl

omit [Finite A] [Finite B] in
private theorem fixed_open_mate {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    mateEquiv
        (ProEtale.openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
        (ProEtale.openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
        (TwoSquare.mk _ _ _ _ (sfFixedOpenRestriction j φ).hom) =
      TwoSquare.mk
        (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
        (sfFixedRestriction Z φ) (sfFixedRestriction U φ)
        (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
        (𝟙 _) := by
  ext N : 1
  simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.id_app,
    NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  slice_lhs 1 2 => exact fixed_normalized j φ _
  erw [Category.comp_id]
  have h := congrArg ((sfFixedRestriction U φ).map)
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).right_triangle_components N)
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at h
  exact h

omit [Finite A] [Finite B] [Finite C] in
private theorem fixed_open_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (M : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfFixedOpenRestriction j (ψ.comp φ)).hom.app M =
      (sfFixedOpenRestriction j φ).hom.app ((sfFixedRestriction U ψ).obj M) ≫
        (sfFixedRestriction Z φ).map ((sfFixedOpenRestriction j ψ).hom.app M) := by
  apply ((ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  slice_lhs 1 2 => exact fixed_normalized j (ψ.comp φ) M
  slice_rhs 1 2 => exact fixed_normalized j φ ((sfFixedRestriction U ψ).obj M)
  have h := congrArg ((sfFixedRestriction U φ).map) (fixed_normalized j ψ M).symm
  simp only [Functor.map_comp] at h
  exact h

private theorem open_mate {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    mateEquiv (sfIntrinsicExtensionByZeroAdjunction j B)
        (sfIntrinsicExtensionByZeroAdjunction j A)
        (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) =
      TwoSquare.mk _ _ _ _ (sfOpenRestrictionCoefficientSquare j φ).inv := by
  let bU := (sfIntrinsicModuleEquivalence U B).symm.toAdjunction
  let aU := (sfIntrinsicModuleEquivalence U A).symm.toAdjunction
  let bZ := (sfIntrinsicModuleEquivalence Z B).toAdjunction
  let aZ := (sfIntrinsicModuleEquivalence Z A).toAdjunction
  let b := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let a := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let s₁ := TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction U φ).hom
  let s₂ := TwoSquare.mk _ _ _ _ (sfFixedOpenRestriction j φ).hom
  let s₃ := TwoSquare.mk _ _ _ _ (sfRealizationRestriction Z φ).inv
  have h := mateEquiv_hcomp (bU.comp b) (aU.comp a) bZ aZ (s₁ ≫ᵥ s₂) s₃
  rw [mateEquiv_hcomp bU aU b a] at h
  dsimp only [s₁, s₂, s₃, aU, bU, aZ, bZ, a, b] at h
  rw [inverse_realization_mate, fixed_open_mate, forward_realization_mate] at h
  have hs : (s₁ ≫ᵥ s₂) ≫ᵥ s₃ =
      TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom := by
    ext M : 1
    simp only [s₁, s₂, s₃, sfOpenRestriction, TwoSquare.vComp,
      TwoSquare.mk, TwoSquare.natTrans, Functor.comp_map, Functor.map_comp,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [s₁, s₂, s₃] at hs
  rw [hs] at h
  change mateEquiv (sfIntrinsicExtensionByZeroAdjunction j B)
    (sfIntrinsicExtensionByZeroAdjunction j A) _ = _ at h
  refine h.trans ?_
  ext M : 1
  simp only [sfOpenRestrictionCoefficientSquare, TwoSquare.hComp,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.id_app, Functor.comp_obj, Functor.comp_map,
    Iso.trans_inv, Iso.symm_inv, Iso.refl_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  all_goals rfl


private theorem open_normalized {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) := by
  intro M
  have h := unit_mateEquiv (sfIntrinsicExtensionByZeroAdjunction j B)
    (sfIntrinsicExtensionByZeroAdjunction j A)
    (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) M
  rw [open_mate] at h
  dsimp only [TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj] at h
  rw [← Category.assoc, ← h]
  simp

/-- The published comparison is the unique comparison inducing identity on the
extension presheaves, equivalently satisfying the displayed open-unit equation.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the fixed-scalar comparison is the uniqueness isomorphism between two
composite left adjoints. Evaluate its unit equation on a section and at 1 in the
coextended module to get the open-unit normalization. Its adjunction mate is thus
the identity restriction square. The realization comparisons are also mates, so
compatibility of mates with pasting identifies the intrinsic comparison's mate
with the inverse coefficient square. The mate unit equation gives normalization.
The open adjunction hom equivalence and cancellation of the coefficient-square
isomorphism give uniqueness. -/
theorem sfOpenRestriction_normalized_unique {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) ∧
      ∀ e : proEtaleCoefficientRestrictScalars U φ ⋙ sfIntrinsicExtensionByZero j A ≅
          sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ,
        SfOpenRestrictionNormalized j φ e → e = sfOpenRestriction j φ := by
  refine ⟨open_normalized j φ, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((sfIntrinsicExtensionByZeroAdjunction j A).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply (cancel_mono ((sfOpenRestrictionCoefficientSquare j φ).hom.app
    ((sfIntrinsicExtensionByZero j B).obj M))).mp
  simpa only [Category.assoc] using (he M).trans ((open_normalized j φ) M).symm

/-- The sheaf comparison cocycle, including both canonical scalar associators.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the fixed-scalar cocycle follows from its unit normalization and
injectivity of the open adjunction hom equivalence. The realization comparison
preserves sections, so its composition agrees with the prescribed intrinsic scalar
compositor. Taking adjunction mates gives the corresponding inverse-realization
composition law. Expand the published open comparison, apply these composition
laws, and use naturality to obtain the stated cocycle. -/
theorem sfOpenRestriction_coefficient_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules U (proEtaleConstantRing U C)) :
    (sfIntrinsicExtensionByZero j A).map
        ((sfCoefficientRestrictionComp U φ ψ).hom.app M) ≫
      (sfOpenRestriction j (ψ.comp φ)).hom.app M =
    (sfOpenRestriction j φ).hom.app ((proEtaleCoefficientRestrictScalars U ψ).obj M) ≫
      (proEtaleCoefficientRestrictScalars Z φ).map
        ((sfOpenRestriction j ψ).hom.app M) ≫
      (sfCoefficientRestrictionComp Z φ ψ).hom.app
        ((sfIntrinsicExtensionByZero j C).obj M) := by
  let N := (sfIntrinsicModuleEquivalence U C).inverse.obj M
  have hn₁ := (sfRealizationRestriction Z φ).inv.naturality
    ((ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).map
        ((sfInverseRealizationRestriction U ψ).hom.app M))
  have hn₂ := (sfRealizationRestriction Z φ).inv.naturality
    ((sfFixedOpenRestriction j ψ).hom.app N)
  have hn₃ := (sfFixedOpenRestriction j φ).hom.naturality
    ((sfInverseRealizationRestriction U ψ).hom.app M)
  simp only [Functor.comp_map] at hn₁ hn₂ hn₃
  simp only [sfOpenRestriction, sfIntrinsicExtensionByZero,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj] at hn₁ hn₂ hn₃ ⊢
  slice_rhs 3 4 => exact hn₁.symm
  slice_rhs 4 5 => exact hn₂.symm
  slice_rhs 5 7 => exact realization_inv_comp Z φ ψ _
  simp only [← (sfIntrinsicModuleEquivalence Z A).functor.map_comp_assoc]
  congr 2
  slice_rhs 2 3 => exact hn₃.symm
  simp only [Category.assoc]
  slice_rhs 3 4 => exact (fixed_open_comp j φ ψ N).symm
  simp only [← Functor.map_comp_assoc]
  rw [inverse_realization_comp]


/-- The identity coefficient law on module sheaves, with canonical identifications.
Source: Stacks Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the canonical identity restriction comparison preserves each section,
by the realization normalization and the equivalence counit identity. Specialize
the coefficient cocycle to two identity homomorphisms, use naturality, and cancel
its first invertible open-comparison component. Equality on sections identifies
the resulting scalar-restricted equation with the required identity equation. -/
theorem sfOpenRestriction_coefficient_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
    (sfOpenRestriction j (RingHom.id R)).hom.app M ≫
        (sfOpenCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).obj M) =
      (sfIntrinsicExtensionByZero j R).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M) := by
  have hc := sfOpenRestriction_coefficient_comp j (RingHom.id R) (RingHom.id R) M
  have hn := (sfOpenRestriction j (RingHom.id R)).hom.naturality
    ((sfOpenCoefficientRestrictionId U R).hom.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [restriction_id_comp, restriction_id_comp] at hc
  change (sfIntrinsicExtensionByZero j R).map
      ((proEtaleCoefficientRestrictScalars U (RingHom.id R)).map
        ((sfOpenCoefficientRestrictionId U R).hom.app M)) ≫
      (sfOpenRestriction j (RingHom.id R)).hom.app M = _ at hc
  rw [hn] at hc
  have hmap := (cancel_epi ((sfOpenRestriction j (RingHom.id R)).hom.app
    ((proEtaleCoefficientRestrictScalars U (RingHom.id R)).obj M))).mp hc
  rw [← Functor.map_comp] at hmap
  ext V x
  exact congrArg (fun f ↦ f.val.app V x) hmap.symm

/-- The same cocycle on all cochain complexes, without a boundedness condition.
Source: Stacks Tag 015F, with Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: apply the sheaf comparisons in every degree. Their naturality makes these
maps and their inverses chain maps. The sheaf cocycle in each degree proves the
chain-map equation; it does not depend on the range of nonzero degrees. -/
theorem sfOpenRestriction_cochain_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (K : CochainComplex (proEtaleRingModules U (proEtaleConstantRing U C)) ℤ) :
    ((sfIntrinsicExtensionByZero j A).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (sfCoefficientRestrictionComp U φ ψ)
          (.up ℤ)).hom.app K) ≫
      (NatIso.mapHomologicalComplex (sfOpenRestriction j (ψ.comp φ))
        (.up ℤ)).hom.app K =
    (NatIso.mapHomologicalComplex (sfOpenRestriction j φ) (.up ℤ)).hom.app
        (((proEtaleCoefficientRestrictScalars U ψ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      ((proEtaleCoefficientRestrictScalars Z φ).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (sfOpenRestriction j ψ) (.up ℤ)).hom.app K) ≫
      (NatIso.mapHomologicalComplex (sfCoefficientRestrictionComp Z φ ψ)
        (.up ℤ)).hom.app
        (((sfIntrinsicExtensionByZero j C).mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sfOpenRestriction_coefficient_comp j φ ψ (K.X n)

/-- The identity coefficient law for arbitrary cochain complexes.
Source: Stacks Tag 015F, with Tags 03DI and 03CY
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: the sheaf identity law holds in each degree, hence it is equality of the
termwise natural chain maps. Naturality also supplies their inverse chain maps. -/
theorem sfOpenRestriction_cochain_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (K : CochainComplex (proEtaleRingModules U (proEtaleConstantRing U R)) ℤ) :
    (NatIso.mapHomologicalComplex (sfOpenRestriction j (RingHom.id R))
        (.up ℤ)).hom.app K ≫
      (NatIso.mapHomologicalComplex (sfOpenCoefficientRestrictionId Z R)
        (.up ℤ)).hom.app
        (((sfIntrinsicExtensionByZero j R).mapHomologicalComplex (.up ℤ)).obj K) =
    ((sfIntrinsicExtensionByZero j R).mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (sfOpenCoefficientRestrictionId U R)
        (.up ℤ)).hom.app K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sfOpenRestriction_coefficient_id j R (K.X n)

/-- The prescribed comparison on unbounded derived categories: exact termwise
localization of the already normalized sheaf comparison, with the exact-functor
composition identifications at its endpoints.
Source: Stacks Tag 015F and categories.tex Tag 04VG
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenRestrictionDerived {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars U φ).mapDerivedCategory ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory ⋙
        (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)

/-- Canonical identification of derived identity coefficient restriction with the
identity functor, localized from the sectionwise identity comparison.
Source: Stacks Tag 015F
(blueprint: lem-sf-open-extension-scalar-restriction-coherence). -/
def sfOpenDerivedCoefficientRestrictionId (T : Scheme.{u}) (R : Type u)
    [CommRing R] [Finite R] :
    (proEtaleCoefficientRestrictScalars T (RingHom.id R)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (sfOpenCoefficientRestrictionId T R) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The prescribed coefficient cocycle on the entire unbounded derived category.
Source: Stacks Tag 015F and categories.tex Tag 04VG
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: all functors are additive and exact by the existing scalar-restriction
and extension-by-zero instances. Cancel the scalar compositors in the sheaf cocycle
to put it in the orientation of the existing exact derived-square composition
theorem. Apply that theorem, take its component at the arbitrary derived object,
and cancel the invertible derived scalar compositors. This uses unbounded exact
localization, with no resolution or degree bounds. -/
theorem sfOpenRestriction_derived_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (K : proEtaleDerivedCategory U C) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp U φ ψ).hom.app K) ≫
      (sfOpenRestrictionDerived j (ψ.comp φ)).hom.app K =
    (sfOpenRestrictionDerived j φ).hom.app
        ((proEtaleCoefficientRestrictScalars U ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory.map
        ((sfOpenRestrictionDerived j ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app
        ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K) := by
  have hq (M : proEtaleRingModules U (proEtaleConstantRing U C)) :
      (sfIntrinsicExtensionByZero j A).map
          ((sfCoefficientRestrictionComp U φ ψ).inv.app M) ≫
        (sfOpenRestriction j φ).hom.app
          ((proEtaleCoefficientRestrictScalars U ψ).obj M) ≫
        (proEtaleCoefficientRestrictScalars Z φ).map
          ((sfOpenRestriction j ψ).hom.app M) =
      (sfOpenRestriction j (ψ.comp φ)).hom.app M ≫
        (sfCoefficientRestrictionComp Z φ ψ).inv.app
          ((sfIntrinsicExtensionByZero j C).obj M) := by
    have h := congrArg (fun t ↦
      (sfIntrinsicExtensionByZero j A).map
        ((sfCoefficientRestrictionComp U φ ψ).inv.app M) ≫ t ≫
      (sfCoefficientRestrictionComp Z φ ψ).inv.app
        ((sfIntrinsicExtensionByZero j C).obj M))
      (sfOpenRestriction_coefficient_comp j φ ψ M)
    simp only [Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app] at h
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.symm
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (proEtaleCoefficientRestrictScalars U ψ) (proEtaleCoefficientRestrictScalars U φ)
    (proEtaleCoefficientRestrictScalars U (ψ.comp φ))
    (proEtaleCoefficientRestrictScalars Z ψ) (proEtaleCoefficientRestrictScalars Z φ)
    (proEtaleCoefficientRestrictScalars Z (ψ.comp φ))
    (sfIntrinsicExtensionByZero j C) (sfIntrinsicExtensionByZero j B)
    (sfIntrinsicExtensionByZero j A)
    (sfOpenRestriction j ψ) (sfOpenRestriction j φ)
    (sfOpenRestriction j (ψ.comp φ))
    (sfCoefficientRestrictionComp U φ ψ).symm
    (sfCoefficientRestrictionComp Z φ ψ).symm hq
  have hk := congrArg (fun e ↦ e.hom.app K) hd
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.mapDerivedCategoryNatIso_symm] at hk
  change (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp U φ ψ).inv.app K) ≫
      (sfOpenRestrictionDerived j φ).hom.app
        ((proEtaleCoefficientRestrictScalars U ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory.map
        ((sfOpenRestrictionDerived j ψ).hom.app K) =
    (sfOpenRestrictionDerived j (ψ.comp φ)).hom.app K ≫
      (sfDerivedCoefficientRestrictionComp Z φ ψ).inv.app
        ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K) at hk
  have h := congrArg (fun t ↦
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
      ((sfDerivedCoefficientRestrictionComp U φ ψ).hom.app K) ≫ t ≫
    (sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app
      ((sfIntrinsicExtensionByZero j C).mapDerivedCategory.obj K)) hk
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] at h
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact h.symm

/-- The identity coefficient comparison on all unbounded derived objects.
Source: Stacks Tag 015F and categories.tex Tag 04VG
(blueprint: lem-sf-open-extension-scalar-restriction-coherence).

Proof: localize the cochain identity equation with the exact factorization
isomorphisms. Precomposition with the localization functor is faithful on natural
transformations, so its equality on every complex proves the derived equation. -/
theorem sfOpenRestriction_derived_id {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (R : Type u) [CommRing R] [Finite R]
    (K : proEtaleDerivedCategory U R) :
    (sfOpenRestrictionDerived j (RingHom.id R)).hom.app K ≫
        (sfOpenDerivedCoefficientRestrictionId Z R).hom.app
          ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj K) =
      (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
        ((sfOpenDerivedCoefficientRestrictionId U R).hom.app K) := by
  have hi (M : proEtaleRingModules U (proEtaleConstantRing U R)) :
      (sfOpenRestriction j (RingHom.id R)).inv.app M ≫
        (sfIntrinsicExtensionByZero j R).map
          ((sfOpenCoefficientRestrictionId U R).hom.app M) =
      (sfOpenCoefficientRestrictionId Z R).hom.app
        ((sfIntrinsicExtensionByZero j R).obj M) := by
    rw [← sfOpenRestriction_coefficient_id j R M]
    simp
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_id
    (sfOpenRestriction j (RingHom.id R)).symm
    (sfOpenCoefficientRestrictionId U R) (sfOpenCoefficientRestrictionId Z R) hi K
  have hs : Functor.mapDerivedCategorySquareIso
        (sfOpenRestriction j (RingHom.id R)).symm =
      (sfOpenRestrictionDerived j (RingHom.id R)).symm := by
    apply Iso.ext
    simp only [sfOpenRestrictionDerived, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs] at hd
  rw [← cancel_epi ((sfOpenRestrictionDerived j (RingHom.id R)).inv.app K)]
  simpa only [sfOpenDerivedCoefficientRestrictionId, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.symm_hom] using hd.symm

end AlgebraicGeometry.Scheme
