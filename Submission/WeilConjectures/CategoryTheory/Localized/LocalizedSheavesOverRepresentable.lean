/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Continuous

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Localized sheaves over a sheafified representable

Source: Stacks Project, Sites, Tag 00Y1, lemma-essential-image-j-shriek, and
lemma-describe-j-shriek in Section 00XZ
(blueprint: lem-weil-pbc-localized-sheaves-over-representable).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

private theorem sigma_ext {C : Type u} [SmallCategory C] {U X : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) {a b : X ⟶ U}
    {s : H.obj (op (Over.mk a))} {t : H.obj (op (Over.mk b))}
    (h : a = b) (hs : H.map (eqToHom (by rw [h])).op t = s) :
    (⟨a, s⟩ : Σ a : X ⟶ U, H.obj (op (Over.mk a))) = ⟨b, t⟩ := by
  subst b
  simpa using congrArg
    (fun t : H.obj (op (Over.mk a)) ↦
      (⟨a, t⟩ : Σ a : X ⟶ U, H.obj (op (Over.mk a)))) hs.symm

private def sigmaRestriction {C : Type u} [SmallCategory C] {U X Y : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) (b : Y ⟶ X)
    (z : Σ a : X ⟶ U, H.obj (op (Over.mk a))) :
    Σ a : Y ⟶ U, H.obj (op (Over.mk a)) :=
  ⟨b ≫ z.1, H.map (Over.homMk b rfl).op z.2⟩

private def sigmaPresheaf {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Type u where
  obj X := Σ a : X.unop ⟶ U, H.obj (op (Over.mk a))
  map b := ↾(sigmaRestriction H b.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.id_comp _)
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

  map_comp b c := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.assoc _ _ _)
    simp only [← Functor.map_comp_apply]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

private def sigmaProjection {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type u) : sigmaPresheaf H ⟶ yoneda.obj U where
  app _ := ↾fun z ↦ z.1
  naturality _ _ _ := rfl

private def sigmaMap {C : Type u} [SmallCategory C] {U : C}
    {H H' : (Over U)ᵒᵖ ⥤ Type u} (f : H ⟶ H') : sigmaPresheaf H ⟶ sigmaPresheaf H' where
  app _ := ↾fun z ↦ ⟨z.1, f.app _ z.2⟩
  naturality X Y b := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    dsimp [sigmaPresheaf, sigmaRestriction]
    congr 1
    exact f.naturality_apply
      (Over.homMk b.unop rfl : Over.mk (b.unop ≫ a) ⟶ Over.mk a).op s

private def sigmaFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) (U : C) :
    Sheaf (K.over U) (Type u) ⥤ Over (yoneda.obj U) where
  obj H := Over.mk (sigmaProjection H.obj)
  map f := Over.homMk (sigmaMap f.hom) (by rfl)
  map_id H := by
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    rfl

private def fibreSubfunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    Subfunctor (F.left.over U).obj where
  obj X := {s | F.hom.hom.app (op X.unop.left) s =
    (toSheafify K (yoneda.obj U)).app (op X.unop.left) X.unop.hom}
  map {X Y} b s hs := by
    change F.hom.hom.app _ (F.left.obj.map b.unop.left.op s) = _
    rw [NatTrans.naturality_apply, hs, ← NatTrans.naturality_apply]
    congr 1
    exact Over.w b.unop

private theorem fibre_isSheaf {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    Presheaf.IsSheaf (K.over U) (fibreSubfunctor K U F).toFunctor := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp (F.left.over U).property)).mpr
  intro X s hs
  change F.hom.hom.app _ s = _
  let G := ((presheafToSheaf K (Type u)).obj (yoneda.obj U)).over U
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated _ hs).ext
  intro Y b hb
  change (sheafify K (yoneda.obj U)).map b.left.op (F.hom.hom.app _ s) =
    (sheafify K (yoneda.obj U)).map b.left.op _
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  change F.hom.hom.app _ (F.left.obj.map b.left.op s) =
    (toSheafify K (yoneda.obj U)).app _ (b.left ≫ X.unop.hom)
  rw [Over.w]
  exact hb

private noncomputable def fibreFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C) :
    Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U)) ⥤ Sheaf (K.over U) (Type u) where
  obj F := ⟨(fibreSubfunctor K U F).toFunctor, fibre_isSheaf K U F⟩
  map {F G} f := ⟨{
    app X := ↾fun s ↦ ⟨f.left.hom.app _ s.val, by
      have h := congrArg (fun t ↦ t.hom.app (op X.unop.left) s.val) (Over.w f)
      exact h.trans s.property⟩
    naturality X Y b := by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact f.left.hom.naturality_apply b.unop.left.op s.val }⟩

private noncomputable abbrev extensionFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C) :=
  sigmaFunctor K U ⋙ Over.post (presheafToSheaf K (Type u))

private def forgetPairs {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) [HasWeakSheafify K (Type u)] (U : C)
    (F : Over ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) :
    sigmaPresheaf ((fibreFunctor K U).obj F).obj ⟶ F.left.obj where
  app _ := ↾fun z ↦ z.2.val
  naturality _ _ _ := rfl

end CategoryTheory
