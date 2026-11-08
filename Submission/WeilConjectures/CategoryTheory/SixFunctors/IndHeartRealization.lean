/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Presentable.Finite

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Realizing ind-objects of a finitely presentable full subcategory

Source: blueprint main-20261015, sk-prop-ind-heart,
`sk-prop-ind-heart-full-faithfulness.proof.md`, paragraphs (2) and the statement's image clause.
(blueprint: det-ind-heart-full-faithfulness-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v u u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor

namespace IndRealization
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (F : C ⥤ D) [HasFilteredColimits D]

private abbrev nerve : D ⥤ Cᵒᵖ ⥤ Type v where
  obj Y := F.op ⋙ yoneda.obj Y
  map f := whiskerLeft F.op (yoneda.map f)

private abbrev obj (Z : Ind C) : D := colimit (Z.presentation.F ⋙ F)

private def leg {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    yoneda.obj X ⟶ (nerve F).obj Y where
  app W := ↾fun g ↦ F.map g ≫ f
  naturality W W' g := by
    ext h
    change F.map (g.unop ≫ h) ≫ f = F.map g.unop ≫ F.map h ≫ f
    rw [F.map_comp, Category.assoc]

private def toNerve (Z : Ind C) {Y : D} (f : obj F Z ⟶ Y) :
    (Ind.inclusion C).obj Z ⟶ (nerve F).obj Y :=
  Z.presentation.isColimit.desc
    { pt := (nerve F).obj Y
      ι :=
        { app i := leg F (colimit.ι (Z.presentation.F ⋙ F) i ≫ f)
          naturality i j a := by
            ext W g
            change F.map (g ≫ Z.presentation.F.map a) ≫
              (colimit.ι (Z.presentation.F ⋙ F) j ≫ f) =
                F.map g ≫ (colimit.ι (Z.presentation.F ⋙ F) i ≫ f)
            rw [F.map_comp, Category.assoc]
            exact congrArg (fun t ↦ F.map g ≫ t) (colimit.w_assoc
              (Z.presentation.F ⋙ F) a f) } }

private def fromNerve (Z : Ind C) {Y : D}
    (g : (Ind.inclusion C).obj Z ⟶ (nerve F).obj Y) : obj F Z ⟶ Y :=
  colimit.desc (Z.presentation.F ⋙ F)
    { pt := Y
      ι :=
        { app i := (g.app (op (Z.presentation.F.obj i)))
            ((Z.presentation.ι.app i).app _ (𝟙 _))
          naturality i j a := by
            dsimp
            simp only [Category.comp_id]
            have hg := g.naturality_apply (Z.presentation.F.map a).op
              ((Z.presentation.ι.app j).app _ (𝟙 _))
            change F.map (Z.presentation.F.map a) ≫ _ = _
            dsimp [nerve] at hg
            rw [← hg]
            congr 1
            have hp := congrArg (fun t ↦ t.app (op (Z.presentation.F.obj i)) (𝟙 _))
              (Z.presentation.ι.naturality a)
            have hn := (Z.presentation.ι.app j).naturality_apply
              (Z.presentation.F.map a).op (𝟙 (Z.presentation.F.obj j))
            dsimp at hn hp
            simp only [Category.id_comp, Category.comp_id] at hn hp
            exact hn.symm.trans hp } }

private lemma toNerve_fac (Z : Ind C) {Y : D} (f : obj F Z ⟶ Y)
    (i : Z.presentation.I) :
    Z.presentation.ι.app i ≫ toNerve F Z f =
      leg F (colimit.ι (Z.presentation.F ⋙ F) i ≫ f) :=
  Z.presentation.isColimit.fac _ i

private def homEquiv (Z : Ind C) (Y : D) :
    (obj F Z ⟶ Y) ≃ ((Ind.inclusion C).obj Z ⟶ (nerve F).obj Y) where
  toFun := toNerve F Z
  invFun := fromNerve F Z
  left_inv f := by
    apply colimit.hom_ext
    intro i
    dsimp [fromNerve]
    rw [colimit.ι_desc]
    have h := congrArg
      (fun t : yoneda.obj (Z.presentation.F.obj i) ⟶ (nerve F).obj Y ↦
        t.app (op (Z.presentation.F.obj i)) (𝟙 _)) (toNerve_fac F Z f i)
    simpa [leg] using h
  right_inv g := by
    apply Z.presentation.isColimit.hom_ext
    intro i
    rw [toNerve_fac]
    ext W h
    dsimp [leg, fromNerve]
    rw [colimit.ι_desc]
    have hg := g.naturality_apply h.op ((Z.presentation.ι.app i).app _ (𝟙 _))
    have hn := (Z.presentation.ι.app i).naturality_apply h.op (𝟙 (Z.presentation.F.obj i))
    dsimp at hg hn ⊢
    simpa using hg.symm.trans
      (congrArg (fun t : ((Ind.inclusion C).obj Z).obj W ↦ (g.app W) t) hn.symm)

private lemma toNerve_comp (Z : Ind C) {Y Y' : D} (f : obj F Z ⟶ Y) (g : Y ⟶ Y') :
    toNerve F Z (f ≫ g) = toNerve F Z f ≫ (nerve F).map g := by
  apply Z.presentation.isColimit.hom_ext
  intro i
  change Z.presentation.ι.app i ≫ toNerve F Z (f ≫ g) =
    Z.presentation.ι.app i ≫ (toNerve F Z f ≫ (nerve F).map g)
  simp only [← Category.assoc, toNerve_fac]
  ext W h
  dsimp [leg]
  simp only [Category.assoc]

private def functor : Ind C ⥤ D where
  obj := obj F
  map {Z W} f := (homEquiv F Z (obj F W)).symm
    ((Ind.inclusion C).map f ≫ toNerve F W (𝟙 _))
  map_id Z := by
    apply (homEquiv F Z _).injective
    rw [Equiv.apply_symm_apply]
    simp
    rfl
  map_comp {Z W T} f g := by
    apply (homEquiv F Z _).injective
    rw [Equiv.apply_symm_apply]
    change _ = toNerve F Z (_ ≫ _)
    rw [toNerve_comp]
    change _ = (homEquiv F Z _) ((homEquiv F Z _).symm _) ≫ _
    rw [Equiv.apply_symm_apply, Category.assoc, ← toNerve_comp, Category.id_comp]
    change _ = (Ind.inclusion C).map f ≫
      (homEquiv F W _) ((homEquiv F W _).symm _)
    rw [Equiv.apply_symm_apply, Functor.map_comp, Category.assoc]

private lemma toNerve_map_comp {Z W : Ind C} (f : Z ⟶ W) {Y : D}
    (g : (functor F).obj W ⟶ Y) :
    toNerve F Z ((functor F).map f ≫ g) =
      (Ind.inclusion C).map f ≫ toNerve F W g := by
  rw [toNerve_comp]
  change (homEquiv F Z _) ((homEquiv F Z _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply, Category.assoc, ← toNerve_comp, Category.id_comp]

private def mappedCocone {J : Type v} [SmallCategory J] (T : J ⥤ Ind C)
    (s : Cocone (T ⋙ functor F)) : Cocone (T ⋙ Ind.inclusion C) where
  pt := (nerve F).obj s.pt
  ι :=
    { app j := toNerve F (T.obj j) (s.ι.app j)
      naturality i j a := by
        dsimp
        rw [Category.comp_id, ← toNerve_map_comp]
        congr 1
        exact s.w a }

private def preserves {J : Type v} [SmallCategory J] [IsFiltered J]
    (T : J ⥤ Ind C) {c : Cocone T} (hc : IsColimit c) :
    IsColimit ((functor F).mapCocone c) where
  desc s := (homEquiv F c.pt s.pt).symm
    ((isColimitOfPreserves (Ind.inclusion C) hc).desc (mappedCocone F T s))
  fac s j := by
    apply (homEquiv F (T.obj j) s.pt).injective
    change toNerve F (T.obj j) ((functor F).map (c.ι.app j) ≫ _) = _
    rw [toNerve_map_comp]
    change _ ≫ (homEquiv F c.pt _) ((homEquiv F c.pt _).symm _) = _
    rw [Equiv.apply_symm_apply]
    exact (isColimitOfPreserves (Ind.inclusion C) hc).fac _ j
  uniq s m hm := by
    change obj F c.pt ⟶ s.pt at m
    change ∀ j, (functor F).map (c.ι.app j) ≫ m = s.ι.app j at hm
    apply (homEquiv F c.pt s.pt).injective
    change toNerve F c.pt m = (homEquiv F c.pt _) ((homEquiv F c.pt _).symm _)
    rw [Equiv.apply_symm_apply]
    apply (isColimitOfPreserves (Ind.inclusion C) hc).hom_ext
    intro j
    change (Ind.inclusion C).map (c.ι.app j) ≫ _ = _
    calc
      _ = toNerve F (T.obj j) ((functor F).map (c.ι.app j) ≫ m) :=
        (toNerve_map_comp F (c.ι.app j) m).symm
      _ = toNerve F (T.obj j) (s.ι.app j) := by rw [hm]
      _ = _ := ((isColimitOfPreserves (Ind.inclusion C) hc).fac
        (mappedCocone F T s) j).symm

private instance : PreservesFilteredColimits (functor F) := by
  constructor
  intro J _ _
  constructor
  intro T
  exact ⟨fun hc ↦ ⟨preserves F T hc⟩⟩

end IndRealization

open IndRealization
namespace CategoryTheory

end CategoryTheory

namespace CategoryTheory
end CategoryTheory
