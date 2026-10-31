/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationChosenComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Transport of compactification words through fixed realizations

Source: Stacks 0F7J--0F7K, conjugation by the fixed realization equivalences.
(blueprint: lem-sp-compactification-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProperOpenCalculus
attribute [local implicit_reducible] H Compactification.copy

variable {A : Scheme.{u} → Prop} (F : ProperOpenCalculus.{u, v, w} A)

set_option linter.checkUnivs false in
/-- Fixed native functors and their comparison to the literal proper/open word.
The comparison is part of the coordinates, not a map recovered by evaluation.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
structure CompactificationRealization where
  obj : {X : Scheme.{u} // A X} → Type w'
  [category (X : {X : Scheme.{u} // A X}) : Category.{v'} (obj X)]
  coordinate (X : {X : Scheme.{u} // A X}) : obj X ≌ F.obj X
  H (X Y : {X : Scheme.{u} // A X}) {f : X.val ⟶ Y.val} [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) : obj X ⥤ obj Y
  comparison (X Y : {X : Scheme.{u} // A X}) {f : X.val ⟶ Y.val} [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) :
    H X Y c hc ⋙ (coordinate Y).functor ≅ (coordinate X).functor ⋙ F.H X Y c hc

namespace CompactificationRealization
attribute [instance] category
variable {F} (R : CompactificationRealization.{u, v, w, v', w'} F) (G : Geometry A)

/-- Transport a known model comparison through a fully faithful target coordinate.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
def refinement (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z) :
    R.H X Y c hc ≅ R.H X Y d hd :=
  ((R.coordinate Y).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (R.comparison X Y c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.comparison G X Y f c d hc hd) ≪≫
        (R.comparison X Y d hd).symm)

/-- Transport the actual binary word through the fixed coordinates.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
def composition (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg : X.val ⟶ Z.val) (wfg : f ≫ g = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact fg]
    (c : Compactification f) (d : Compactification g) (e : Compactification fg)
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    R.H X Y c hc ⋙ R.H Y Z d hd ≅ R.H X Z e he :=
  ((R.coordinate Z).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.H X Y c hc) (R.comparison Y Z d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (R.comparison X Y c hc) (F.H Y Z d hd) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor
        (F.namedBinary G X Y Z f g fg wfg c d e hc hd he) ≪≫
      (R.comparison X Z e he).symm)

/-- The identity word transported through the fixed coordinates.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
def identity (X : {X : Scheme.{u} // A X})
    (c : Compactification (𝟙 X.val)) (hc : A c.Z) :
    R.H X X c hc ≅ 𝟭 (R.obj X) :=
  ((R.coordinate X).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (R.comparison X X c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.chosenIdentity G X c hc) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The refinement map is pinned by its image under the faithful coordinate.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
theorem refinement_map (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z) (M : R.obj X) :
    (R.coordinate Y).functor.map ((R.refinement G X Y f c d hc hd).hom.app M) =
      (R.comparison X Y c hc).hom.app M ≫
        (F.comparison G X Y f c d hc hd).hom.app ((R.coordinate X).functor.obj M) ≫
          (R.comparison X Y d hd).inv.app M := by
  have h := ((R.coordinate Y).fullyFaithfulFunctor.whiskeringRight _).map_preimage
    (R.comparison X Y c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.comparison G X Y f c d hc hd) ≪≫
        (R.comparison X Y d hd).symm).hom
  exact NatTrans.congr_app h M

/-- The composition map is the actual conjugated binary word at every native object.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
theorem composition_map (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg : X.val ⟶ Z.val) (wfg : f ≫ g = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact fg]
    (c : Compactification f) (d : Compactification g) (e : Compactification fg)
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) (M : R.obj X) :
    (R.coordinate Z).functor.map
      ((R.composition G X Y Z f g fg wfg c d e hc hd he).hom.app M) =
      (R.comparison Y Z d hd).hom.app ((R.H X Y c hc).obj M) ≫
        (F.H Y Z d hd).map ((R.comparison X Y c hc).hom.app M) ≫
        (F.namedBinary G X Y Z f g fg wfg c d e hc hd he).hom.app
          ((R.coordinate X).functor.obj M) ≫ (R.comparison X Z e he).inv.app M := by
  have h := ((R.coordinate Z).fullyFaithfulFunctor.whiskeringRight _).map_preimage
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.H X Y c hc) (R.comparison Y Z d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (R.comparison X Y c hc) (F.H Y Z d hd) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor
        (F.namedBinary G X Y Z f g fg wfg c d e hc hd he) ≪≫
      (R.comparison X Z e he).symm).hom
  simpa only [composition, identity, Functor.FullyFaithful.preimageIso_hom,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app h M

/-- Identity transport at a native object.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
theorem identity_map (X : {X : Scheme.{u} // A X})
    (c : Compactification (𝟙 X.val)) (hc : A c.Z) (M : R.obj X) :
    (R.coordinate X).functor.map ((R.identity G X c hc).hom.app M) =
      (R.comparison X X c hc).hom.app M ≫
        (F.chosenIdentity G X c hc).hom.app ((R.coordinate X).functor.obj M) := by
  have h := ((R.coordinate X).fullyFaithfulFunctor.whiskeringRight _).map_preimage
    (R.comparison X X c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.chosenIdentity G X c hc) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm).hom
  simpa only [composition, identity, Functor.FullyFaithful.preimageIso_hom,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app h M

@[simp] theorem refinement_refl (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) :
    R.refinement G X Y f c c hc hc = Iso.refl _ := by
  apply Iso.ext
  ext M
  apply (R.coordinate Y).functor.map_injective
  simp [refinement_map, comparison_refl]

@[simp] theorem refinement_trans (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    R.refinement G X Y f c d hc hd ≪≫ R.refinement G X Y f d e hd he =
      R.refinement G X Y f c e hc he := by
  apply Iso.ext
  ext M
  apply (R.coordinate Y).functor.map_injective
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, refinement_map]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := NatTrans.congr_app (congrArg Iso.hom
    (F.comparison_trans G X Y f c d e hc hd he)) ((R.coordinate X).functor.obj M)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
    congrArg (fun a ↦ (R.comparison X Y c hc).hom.app M ≫ a ≫
      (R.comparison X Y e he).inv.app M) h

/-- Naturality pins the image of every native support morphism.
Source: blueprint Local pairs (blueprint: lem-sp-compactification-realization). -/
theorem support_map (X Y : {X : Scheme.{u} // A X}) {f : X.val ⟶ Y.val}
    [QuasiCompact f] (c : Compactification f) (hc : A c.Z)
    {M N : R.obj X} (t : M ⟶ N) :
    (R.coordinate Y).functor.map ((R.H X Y c hc).map t) =
      (R.comparison X Y c hc).hom.app M ≫
        (F.H X Y c hc).map ((R.coordinate X).functor.map t) ≫
          (R.comparison X Y c hc).inv.app N := by
  have h := (R.comparison X Y c hc).hom.naturality t
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  simp

private theorem map_natIso_inv_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) {I J : C ⥤ D} (e : I ≅ J) (M : C)
    {N : E} (t : F.obj (J.obj M) ⟶ N) :
    F.map (e.inv.app M) ≫ F.map (e.hom.app M) ≫ t = t := by
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id_app,
    F.map_id, Category.id_comp]

/-- Refinements commute with native binary composition before any evaluation.
Source: Stacks 0F7J (blueprint: lem-sp-compactification-realization).

Proof: apply the faithful target coordinate and expand the three defining words.
Naturality of the model refinement moves it past the coordinate comparisons.
The inverse coordinate factors cancel. The remaining middle equation is model
binary refinement compatibility. This also proves the result on empty inputs. -/
theorem composition_refinement (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c c' : Compactification f) (d d' : Compactification g)
    (e e' : Compactification (f ≫ g))
    (hc : A c.Z) (hc' : A c'.Z) (hd : A d.Z) (hd' : A d'.Z)
    (he : A e.Z) (he' : A e'.Z) (M : R.obj X) :
    (R.H Y Z d hd).map ((R.refinement G X Y f c c' hc hc').hom.app M) ≫
      (R.refinement G Y Z g d d' hd hd').hom.app ((R.H X Y c' hc').obj M) ≫
        (R.composition G X Y Z f g (f ≫ g) rfl c' d' e' hc' hd' he').hom.app M =
      (R.composition G X Y Z f g (f ≫ g) rfl c d e hc hd he).hom.app M ≫
        (R.refinement G X Z (f ≫ g) e e' he he').hom.app M := by
  apply (R.coordinate Z).functor.map_injective
  simp only [Functor.map_comp, support_map, refinement_map, composition_map]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn := (F.comparison G Y Z g d d' hd hd').hom.naturality
    ((R.comparison X Y c' hc').inv.app M)
  try dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  try simp only [Category.assoc] at hn
  rw [← Category.assoc ((F.H Y Z d hd).map ((R.comparison X Y c' hc').inv.app M)), hn]
  simp only [Category.assoc]
  have hn' := (F.comparison G Y Z g d d' hd hd').hom.naturality
    ((F.comparison G X Y f c c' hc hc').hom.app ((R.coordinate X).functor.obj M))
  try dsimp only [Functor.comp_map, Functor.comp_obj] at hn'
  have ht := NatTrans.congr_app
    (F.binary_refinement G X Y Z f g c c' d d' e e' hc hc' hd hd' he he')
    ((R.coordinate X).functor.obj M)
  simp only [NatIso.hcomp_hom, NatTrans.comp_app, NatTrans.hcomp_app] at ht
  rw [← hn'] at ht
  try simp only [Category.assoc] at ht
  simp only [namedBinary_rfl]
  simp only [map_natIso_inv_hom]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ (R.comparison Y Z d hd).hom.app ((R.H X Y c hc).obj M) ≫
      (F.H Y Z d hd).map ((R.comparison X Y c hc).hom.app M) ≫ t ≫
      (R.comparison X Z e' he').inv.app M) ht

/-- Native composition is associative under the fixed faithful coordinates.
Source: Stacks 0F7K (blueprint: lem-sp-compactification-realization).

Proof: apply the faithful last coordinate and expand the four binary words.
Naturality of the last support comparison and cancellation of the comparison
for the middle composite leave model associativity. Naturality of the model
second binary word moves the first coordinate comparison through it, yielding
the other side. All equalities are in the derived category itself. -/
theorem composition_associativity (X Y Z W : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (h : Z.val ⟶ W.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (cd : Compactification (f ≫ g)) (de : Compactification (g ≫ h))
    (cde : Compactification (f ≫ g ≫ h))
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
    (hcd : A cd.Z) (hde : A de.Z) (hcde : A cde.Z) (M : R.obj X) :
    (R.H Z W e he).map
        ((R.composition G X Y Z f g (f ≫ g) rfl c d cd hc hd hcd).hom.app M) ≫
      (R.composition G X Z W (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)
        cd e cde hcd he hcde).hom.app M =
      (R.composition G Y Z W g h (g ≫ h) rfl d e de hd he hde).hom.app
          ((R.H X Y c hc).obj M) ≫
        (R.composition G X Y W f (g ≫ h) (f ≫ g ≫ h) rfl c de cde hc hde hcde).hom.app M := by
  apply (R.coordinate W).functor.map_injective
  simp only [Functor.map_comp, support_map, composition_map]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  try simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  try simp only [Functor.map_comp]
  have ht := NatTrans.congr_app
    (F.namedBinary_associativity G X Y Z W f g h c d e cd de cde
      hc hd he hcd hde hcde) ((R.coordinate X).functor.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at ht
  have hn := (F.binary G Y Z W g h d e de hd he hde).hom.naturality
    ((R.comparison X Y c hc).hom.app M)
  try dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [namedBinary_rfl] at ht ⊢
  simp only [map_natIso_inv_hom, Functor.comp_obj]
  try simp only [Category.assoc] at ht
  have ht' := congrArg
    (fun t ↦ (R.comparison Z W e he).hom.app ((R.H Y Z d hd).obj ((R.H X Y c hc).obj M)) ≫
      (F.H Z W e he).map ((R.comparison Y Z d hd).hom.app ((R.H X Y c hc).obj M)) ≫
      (F.H Z W e he).map ((F.H Y Z d hd).map ((R.comparison X Y c hc).hom.app M)) ≫
      t ≫ (R.comparison X W cde hcde).inv.app M) ht
  simp only [Category.assoc] at ht'
  conv_rhs at ht' =>
    rw [← Category.assoc ((F.H Z W e he).map
      ((F.H Y Z d hd).map ((R.comparison X Y c hc).hom.app M))), hn]
  simpa only [Category.assoc] using ht'

/-- Left identity for native composition.
Source: Stacks 0F7K (blueprint: lem-sp-compactification-realization). -/
theorem composition_left (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 X.val)) (hi : A i.Z) (M : R.obj X) :
    (R.composition G X X Y (𝟙 X.val) f f (Category.id_comp f) i c c hi hc hc).hom.app M =
      (R.H X Y c hc).map ((R.identity G X i hi).hom.app M) := by
  apply (R.coordinate Y).functor.map_injective
  simp only [composition_map, support_map, identity_map, Functor.map_comp]
  rw [F.namedBinary_left G X Y f c hc i hi]
  simp

/-- Right identity for native composition.
Source: Stacks 0F7K (blueprint: lem-sp-compactification-realization). -/
theorem composition_right (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 Y.val)) (hi : A i.Z) (M : R.obj X) :
    (R.composition G X Y Y f (𝟙 Y.val) f (Category.comp_id f) c i c hc hi hc).hom.app M =
      (R.identity G Y i hi).hom.app ((R.H X Y c hc).obj M) := by
  apply (R.coordinate Y).functor.map_injective
  simp only [composition_map, identity_map]
  rw [F.namedBinary_right G X Y f c hc i hi]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.assoc]
  have hn := (F.chosenIdentity G Y i hi).hom.naturality
    ((R.comparison X Y c hc).hom.app M)
  dsimp only [Functor.comp_obj, Functor.id_map] at hn
  simp only [Functor.comp_obj, Functor.id_obj] at hn ⊢
  try simp only [Category.assoc]
  rw [← Category.assoc ((F.H Y Y i hi).map ((R.comparison X Y c hc).hom.app M)), hn]
  simp

end CompactificationRealization
end AlgebraicGeometry.ProperOpenCalculus
