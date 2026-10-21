/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
import all Sheaf.AlgebraicGeometry.FiniteFreeDirectImageBalancingCoherence
import all Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence

/-!
# Intrinsic compact-support restriction of scalars

Source: Stacks Project, Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).

The open comparison is the published section-normalized intrinsic comparison.
The proper comparison is the inverse of the published K-injective-normalized ring-sheaf
comparison. Their composite acts on exactly the compact-support functors used by b.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The specified compact-support restriction comparison on intrinsic constant-ring modules.
Source: Stacks Tags 03DI and 0D6E
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
def intrinsicCompactSupportRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (h : Z ⟶ Y) :
    scalarRestriction φ X ⋙ reductionCompactSupport A j h ≅
      reductionCompactSupport B j h ⋙ scalarRestriction φ Y :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ))
      (directImageConstantPush A h) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j B).mapDerivedCategory
      (proEtaleRingRestrictionDerivedDirectImage h
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
        (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift φ))).symm).symm

/-- The published ring-sheaf comparison in the constant-coefficient coordinates.
Source: Stacks Tag 0D6E (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
private abbrev imageRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y) :=
  proEtaleRingRestrictionDerivedDirectImage h
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
    (proEtaleConstantInverseImageMap_naturality h
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The sectionwise identity before deriving the direct-image comparison.
Source: Stacks Tag 0D6E (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
private abbrev ordinaryImageRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y) :=
  proEtaleRingRestrictionDirectImage h
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
    (proEtaleConstantInverseImageMap_naturality h
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The ordinary comparison preserves every section, by its defining normalization.
Source: Stacks Tag 0D6E (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
private theorem ordinaryImageRestriction_apply
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y)
    (M : proEtaleRingModules Z (proEtaleConstantRing Z B)) (V : Y.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange h).op.obj V)) :
    ((ordinaryImageRestriction φ h).hom.app M).val.app V x = x := by
  exact (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique h
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
      (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
      (proEtaleConstantInverseImageMap_naturality h
        (CommRingCat.ofHom (RingHom.ulift φ))).symm)).1 M V x

/-- The inverse coefficient associator preserves sections too: cancel its hom.
Source: Stacks Tag 03DA (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
private theorem restrictionComp_inv_apply
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V) :
    ((sfCoefficientRestrictionComp T φ ψ).inv.app M).val.app V x = x := by
  have he := congrArg (fun k :
      (proEtaleCoefficientRestrictScalars T (ψ.comp φ)).obj M ⟶
        (proEtaleCoefficientRestrictScalars T (ψ.comp φ)).obj M ↦ k.val.app V x)
    ((sfCoefficientRestrictionComp T φ ψ).inv_hom_id_app M)
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Scheme.restriction_comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using he

/-- Paste the three normalized ring-sheaf direct-image squares. The proved generic
unit-normalization calculation applies because all ordinary maps preserve sections.
Source: Stacks Tag 0D6E (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
private theorem imageRestriction_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (h : Z ⟶ Y) :
    imageRestriction (ψ.comp φ) h =
      Functor.isoWhiskerLeft (directImageConstantPush C h)
          (sfDerivedCoefficientRestrictionComp Y φ ψ).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (imageRestriction ψ h) (scalarRestriction φ Y) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (scalarRestriction ψ Z) (imageRestriction φ h) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sfDerivedCoefficientRestrictionComp Z φ ψ)
          (directImageConstantPush A h) := by
  apply Scheme.FiniteFreeDirectImage.rightTower
    (proEtaleConstantRingPushforward A h) (proEtaleConstantRingPushforward B h)
    (proEtaleConstantRingPushforward C h)
    (proEtaleCoefficientRestrictScalars Y φ) (proEtaleCoefficientRestrictScalars Y ψ)
    (proEtaleCoefficientRestrictScalars Y (ψ.comp φ))
    (proEtaleCoefficientRestrictScalars Z φ) (proEtaleCoefficientRestrictScalars Z ψ)
    (proEtaleCoefficientRestrictScalars Z (ψ.comp φ))
    (sfCoefficientRestrictionComp Y φ ψ) (sfCoefficientRestrictionComp Z φ ψ)
    (imageRestriction φ h) (imageRestriction ψ h) (imageRestriction (ψ.comp φ) h)
    (ordinaryImageRestriction φ h) (ordinaryImageRestriction ψ h)
    (ordinaryImageRestriction (ψ.comp φ) h)
  · intro K
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique h
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
        (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift φ))).symm)).1 K
  · intro K
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique h
        (proEtaleConstantRing Y B) (proEtaleConstantRing Y C)
        (proEtaleConstantRing Z B) (proEtaleConstantRing Z C)
        (proEtaleConstantRingMap (T := Y) ψ) (proEtaleConstantRingMap (T := Z) ψ)
        (proEtaleConstantRingComparison h B) (proEtaleConstantRingComparison h C)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift ψ))).symm)).1 K
  · intro K
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique h
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y C)
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z C)
        (proEtaleConstantRingMap (T := Y) (ψ.comp φ))
        (proEtaleConstantRingMap (T := Z) (ψ.comp φ))
        (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h C)
        (proEtaleConstantInverseImageMap_naturality h
          (CommRingCat.ofHom (RingHom.ulift (ψ.comp φ)))).symm)).1 K
  · intro N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [Scheme.FiniteFreeDirectImage.direct_map_section h
      (proEtaleConstantRing Y A) (proEtaleConstantRing Z A)
      (proEtaleConstantRingComparison h A)
      ((sfCoefficientRestrictionComp Z φ ψ).hom.app N) V]
    erw [Scheme.FiniteFreeDirectImage.restriction_map_section
      (proEtaleConstantRingMap (T := Y) φ)]
    rw [Scheme.restriction_comp_apply, restrictionComp_inv_apply]
    erw [ordinaryImageRestriction_apply, ordinaryImageRestriction_apply,
      ordinaryImageRestriction_apply]

/-- Invert the pasted square and cancel the source coefficient associator.
Source: Stacks Tag 0D6E (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
private theorem imageRestriction_inv_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (h : Z ⟶ Y) (M : proEtaleDerivedCategory Z C) :
    (directImageConstantPush A h).map
        ((sfDerivedCoefficientRestrictionComp Z φ ψ).hom.app M) ≫
      (imageRestriction (ψ.comp φ) h).inv.app M =
    (imageRestriction φ h).inv.app ((scalarRestriction ψ Z).obj M) ≫
      (scalarRestriction φ Y).map ((imageRestriction ψ h).inv.app M) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((directImageConstantPush C h).obj M) := by
  have hi := congrArg (fun e ↦ e.inv.app M) (imageRestriction_comp φ ψ h)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id] at hi
  rw [hi]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Restriction comparisons compose along coefficient maps, with the termwise scalar
restriction associator. Source: Stacks Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: use the proved derived open-extension cocycle. For direct image, the
sectionwise identity ordinary comparisons paste compatibly with the canonical
coefficient associators. Apply the proved generic right-derived unit-normalization
pasting calculation to the published ring-sheaf comparisons and invert the resulting
isomorphism equality. Whisker the open equality by direct image, apply the direct-image
cocycle on the extended object, and use naturality of the first direct-image comparison
on the second open comparison. Associativity gives the displayed composite. -/
theorem intrinsicCompactSupportRestriction_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : Γ(Y, ⊤)))
    (c : Compactification f) (L : proEtaleDerivedCategory X C) :
    (reductionCompactSupport A c.i c.g).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app L) ≫
      (intrinsicCompactSupportRestriction (ψ.comp φ) c.i c.g).hom.app L =
    (intrinsicCompactSupportRestriction φ c.i c.g).hom.app
        ((scalarRestriction ψ X).obj L) ≫
      (scalarRestriction φ Y).map
        ((intrinsicCompactSupportRestriction ψ c.i c.g).hom.app L) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((reductionCompactSupport C c.i c.g).obj L) := by
  have ho := sfOpenRestriction_derived_comp c.i φ ψ L
  have hp := imageRestriction_inv_comp φ ψ c.g
    ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj L)
  have hn := (imageRestriction φ c.g).inv.naturality
    ((sfOpenRestrictionDerived c.i ψ).hom.app L)
  change (directImageConstantPush A c.g).map
      ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app L)) ≫
    (directImageConstantPush A c.g).map
      ((sfOpenRestrictionDerived c.i (ψ.comp φ)).hom.app L) ≫
    (imageRestriction (ψ.comp φ) c.g).inv.app
      ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj L) =
    ((directImageConstantPush A c.g).map
        ((sfOpenRestrictionDerived c.i φ).hom.app ((scalarRestriction ψ X).obj L)) ≫
      (imageRestriction φ c.g).inv.app
        ((sfIntrinsicExtensionByZero c.i B).mapDerivedCategory.obj
          ((scalarRestriction ψ X).obj L))) ≫
    (scalarRestriction φ Y).map
      ((directImageConstantPush B c.g).map
          ((sfOpenRestrictionDerived c.i ψ).hom.app L) ≫
        (imageRestriction ψ c.g).inv.app
          ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj L)) ≫
    (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
      ((directImageConstantPush C c.g).obj
        ((sfIntrinsicExtensionByZero c.i C).mapDerivedCategory.obj L))
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, ho, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hp]
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rfl

end AlgebraicGeometry.ProEtale
