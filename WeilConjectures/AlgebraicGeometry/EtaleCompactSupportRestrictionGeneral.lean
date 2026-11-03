/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import Mathlib.CategoryTheory.Sites.Sheaf
/-! # Bounded-below restriction of the canonical etale compact-support compositor

Source: the ordered exterior-product and comparison paragraphs of
sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Compactification.ofComp Compactification.restrict
  Compactification.comp
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar upperStar openImmersionLowerShriek
attribute [local irreducible] native_unbounded_triangle_iso native_bounded_triangle_iso
  rightDerivedLowerShriekOfCompactificationPlusCompatibility
private theorem native_comparison_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f]
    (c d : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) d).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app K ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  let B := ModuleCat.{u + 1} A
  have hf := refinement_comparison_plus A (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) K
  have hs := refinement_comparison_plus A (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) K
  have hi := square_inverse
    (DerivedCategory.Plus.ι.mapIso ((asIso
      (rightDerivedLowerShriekOfCompactificationPlusComparison B
        (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).app K))
    ((asIso (rightDerivedLowerShriekOfCompactificationComparison B
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).app
        (DerivedCategory.Plus.ι.obj K))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility B d).hom.app K)
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility B
      (Compactification.inf c d)).hom.app K)
    (by simpa only [Functor.mapIso_hom, Iso.app_hom, asIso_hom] using hs)
  simp only [Functor.mapIso_inv, Iso.app_inv, asIso_inv] at hi
  simp only [rightDerivedLowerShriekOfCompactificationPlusIso,
    rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
  erw [hi, ← Category.assoc, hf, Category.assoc]

private theorem inverse_iso_paste
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F F' : C ⥤ D} (G : D ⥤ E) {H J : C ⥤ E}
    (a : H ≅ J) (b : J ≅ F ⋙ G) (c : F ≅ F') :
    (a ≪≫ b ≪≫ Functor.isoWhiskerRight c G).inv =
      NatTrans.hcomp c.inv (𝟙 G) ≫ b.inv ≫ a.inv := by
  ext K
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, NatTrans.hcomp_app, NatTrans.id_app,
    Category.assoc]
  erw [Category.id_comp]

private theorem native_comparison_inverse_plus
  (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (cf cd : Compactification f)
  (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A cf cd).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) cd).hom.app L =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cf).hom.app L ≫
      (rightDerivedLowerShriekOfCompactificationIso A cd cf).inv.app
        (DerivedCategory.Plus.ι.obj L) := by
  have hi := square_inverse
    (DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlusIso A cd cf).app L))
    ((rightDerivedLowerShriekOfCompactificationIso A cd cf).app (DerivedCategory.Plus.ι.obj L))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cd).hom.app L)
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cf).hom.app L)
    (native_comparison_plus A f cd cf L)
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
    ← rightDerivedLowerShriekOfCompactificationPlusIso_symm A cd cf,
    Iso.symm_hom] using hi

private theorem native_comparison_self_plus
  (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  (c : Compactification f)
  (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c c).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app L =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).hom.app L ≫
      (𝟙 _ : rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c ⟶ _).app (DerivedCategory.Plus.ι.obj L) := by
  simp only [rightDerivedLowerShriekOfCompactificationPlusIso_refl,
    Iso.refl_hom, NatTrans.id_app]
  erw [DerivedCategory.Plus.ι.map_id, Category.id_comp, Category.comp_id]

private theorem triangle_restriction_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (cf : Compactification f) (cfg : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (ε : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg ⟶
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg)
    (εp : rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ⋙
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) T.cg ⟶
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cfg)
    (hu : ε = NatTrans.hcomp
          (rightDerivedLowerShriekOfCompactificationIso A T.cf cf).inv
          (𝟙 (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg)) ≫
        (native_unbounded_triangle_iso A T).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A T.cfg cfg).hom)
    (hb : εp = NatTrans.hcomp
          (rightDerivedLowerShriekOfCompactificationPlusIso A cf T.cf).hom
          (rightDerivedLowerShriekOfCompactificationPlusIso A T.cg T.cg).hom ≫
        (native_bounded_triangle_iso (ModuleCat.{u + 1} A) T).hom ≫
        (rightDerivedLowerShriekOfCompactificationPlusIso A T.cfg cfg).hom)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    DerivedCategory.Plus.ι.map (εp.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility B cfg).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility B T.cg).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus B cf).obj K) ≫
      (rightDerivedLowerShriekOfCompactification B T.cg).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility B cf).hom.app K) ≫
      ε.app (DerivedCategory.Plus.ι.obj K) := by
  dsimp only
  rw [hu, hb]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [native_comparison_plus A (f ≫ g) T.cfg cfg K]
  rw [reassoc_of% (triangle_comp_plus A T K)]
  simp only [NatTrans.hcomp_app, Functor.map_comp, Category.assoc]
  have hn := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) T.cg).hom.naturality
    ((rightDerivedLowerShriekOfCompactificationPlusIso A cf T.cf).hom.app K)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [reassoc_of% (native_comparison_self_plus A g T.cg
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf).obj K))]
  simp only [NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [native_comparison_inverse_plus A f cf T.cf K]
  simp only [Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc]

/-- Bounded-below restriction of the canonical etale compact-support compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered composition and comparison;
parent proof Step 2 (blueprint: lem-pur-etale-compact-support-restriction-general).

Proof: Compare two compactifications through their common infimum, using the bounded/unbounded
refinement squares. Invert the second square and paste it with the first. For the chosen
ofRestrict triangle, use this comparison on its first and composite faces, and the identity
on its second face. The triangle inclusion square is already proved. The bounded and native
compositor definitions give the same triangle word. Naturality pastes its four faces
to prove the equation. The argument uses only the displayed quasi-compactness and compactifications.
In particular it does not add a Noetherian assumption to the coordinate statement. -/
theorem compactSupportCompositionPlusCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (rightDerivedLowerShriekCompIso A f g).inv.app (DerivedCategory.Plus.ι.obj K) := by
  let B := ModuleCat.{u + 1} A
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let T := Compactification.Triangle.ofRestrict d e
  let cf := HasCompactification.compactification f
  let cfg := HasCompactification.compactification (f ≫ g)
  have hb := compositor_middle_transport _ _ _ _
    (congrArg Iso.hom (native_bounded_triangle_iso_eq B T).symm)
    (rightDerivedLowerShriekPlusCompIso_hom_eq A T)
  have hu : (rightDerivedLowerShriekCompIso A f g).inv =
      NatTrans.hcomp (rightDerivedLowerShriekIso A e.restrict).inv
          (𝟙 (rightDerivedLowerShriek B g)) ≫
        (native_unbounded_triangle_iso A T).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A T.cfg cfg).hom := by
    rw [native_unbounded_triangle_ofRestrict]
    exact inverse_iso_paste (rightDerivedLowerShriek B g)
      (rightDerivedLowerShriekIso A (d.comp e)).symm
      (rightDerivedLowerShriekOfCompactificationCompIso A d e).symm
      (rightDerivedLowerShriekIso A e.restrict)
  have hp := triangle_restriction_plus A f g cf cfg T
    (rightDerivedLowerShriekCompIso A f g).inv
    (rightDerivedLowerShriekPlusCompIso A f g).hom hu hb K
  exact hp
end AlgebraicGeometry.Etale
