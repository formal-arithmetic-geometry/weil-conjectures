/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C1 and X2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

/-!
# Identity and pasting laws of derived square isomorphisms

Source: Stacks Project, Remarks 0E46 and 0E47
(blueprint: lem-weil-pbc-derived-square-iso-pasting).

The node's closing sentence (the same three identities for the sheaf-level square isomorphisms
`AlgebraicGeometry.Etale.squareUpperStarIso`) is stated in the source repository by
`AlgebraicGeometry.Etale.squareUpperStarIso_id`, `squareUpperStarIso_paste_horiz_hom` and
`squareUpperStarIso_paste_vert_hom` (`WeilConjectures.SixFunctors.BaseChange.Pasting`,
`.DerivedPasting`; node lem-weil-pbc-square-iso-pasting) and is not restated here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private lemma cancel_mapped_inverse
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) {G H : C ⥤ D} (α : G ≅ H) (K : C) {T : E}
    (f : F.obj (G.obj K) ⟶ T) (g : F.obj (H.obj K) ⟶ T) :
    F.map (α.symm.hom.app K) ≫ f = g ↔ f = F.map (α.hom.app K) ≫ g :=
  Iso.inv_comp_eq (F.mapIso (α.app K))

private lemma cancel_component_inverse
    {C D : Type*} [Category C] [Category D]
    {G H : C ⥤ D} (α : G ≅ H) (K : C) {T : D}
    (f : G.obj K ⟶ T) (g : H.obj K ⟶ T) :
    α.symm.hom.app K ≫ f = g ↔ f = α.hom.app K ≫ g :=
  Iso.inv_comp_eq (α.app K)

section

variable (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

private lemma comparison_diagonal
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (d : X' ⟶ Y) (hd : d = g' ≫ f) :
    pullbackSquareComparison A sq =
      (upperStarCompDerivedPlus A f' g d (hd.trans sq.w)).symm ≪≫
        upperStarCompDerivedPlus A g' f d hd := by
  subst hd
  exact pullbackSquareComparison_eq A sq

@[reassoc]
private lemma map_comp_hom_comp_inv
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A)) :
    (upperStar A f).mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus A g h gh hgh).hom.app K) ≫
      (upperStarCompDerivedPlus A f g fg hfg).inv.app
        ((upperStar A h).mapDerivedCategoryPlus.obj K) =
    (upperStarCompDerivedPlus A f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app K ≫
      (upperStarCompDerivedPlus A fg h fgh hfgh).hom.app K := by
  have key := NatTrans.congr_app
    (upperStarCompDerivedPlus_assoc A f g h fg gh fgh hfg hgh hfgh) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  simpa using comp_inv_eq_inv_comp_of_eq _ _ _ _ key

@[reassoc]
private lemma comp_hom_map_comp_inv
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A)) :
    (upperStarCompDerivedPlus A f g fg hfg).hom.app
        ((upperStar A h).mapDerivedCategoryPlus.obj K) ≫
      (upperStar A f).mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus A g h gh hgh).inv.app K) =
    (upperStarCompDerivedPlus A fg h fgh hfgh).inv.app K ≫
      (upperStarCompDerivedPlus A f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K := by
  have key := NatTrans.congr_app
    (upperStarCompDerivedPlus_assoc A f g h fg gh fgh hfg hgh hfgh) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have hh := comp_inv_eq_inv_comp_of_eq _ _ _ _ key.symm
  rwa [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at hh

private lemma comparison_id {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (pullbackSquareComparison A (IsPullback.id_horiz f).toCommSq).hom.app K =
      (upperStar A f).mapDerivedCategoryPlus.map ((upperStarIdDerivedPlus A Y).hom.app K) ≫
        (upperStarIdDerivedPlus A X).inv.app
            ((upperStar A f).mapDerivedCategoryPlus.obj K) := by
  rw [comparison_diagonal A _ f (Category.id_comp f).symm]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  have hr := NatTrans.congr_app (upperStarCompDerivedPlus_id_right A f) K
  have hl := NatTrans.congr_app (upperStarCompDerivedPlus_id_left A f) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app] at hr hl
  apply (cancel_mono ((upperStarIdDerivedPlus A X).hom.app
    ((upperStar A f).mapDerivedCategoryPlus.obj K))).1
  simp only [Category.assoc, hl, Iso.inv_hom_id_app, Category.comp_id]
  have ht := (Iso.inv_comp_eq
    ((upperStarCompDerivedPlus A f (𝟙 Y) f (Category.comp_id f).symm).app K)).mpr hr.symm
  exact (Category.comp_id _).symm.trans (ht.trans (Category.comp_id _).symm)

private lemma comparison_horiz
    {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (upperStar A f'').mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus A h g).symm.hom.app K) ≫
      (pullbackSquareComparison A sq).hom.app K =
        (pullbackSquareComparison A sq₂).hom.app
            ((upperStar A g).mapDerivedCategoryPlus.obj K) ≫
        (upperStar A h').mapDerivedCategoryPlus.map
          ((pullbackSquareComparison A sq₁).hom.app K) ≫
        (upperStarCompDerivedPlus A h' g').symm.hom.app
          ((upperStar A f).mapDerivedCategoryPlus.obj K) := by
  apply (cancel_mapped_inverse (upperStar A f'').mapDerivedCategoryPlus
    (upperStarCompDerivedPlus A h g) K _ _).mpr
  simp only [pullbackSquareComparison_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [map_comp_hom_comp_inv_assoc A f'' h g (h' ≫ f') (h ≫ g)
      ((h' ≫ g') ≫ f) sq₂.w rfl (by rw [Category.assoc, sq₁.w, Category.assoc]),
    comp_hom_map_comp_inv_assoc A h' f' g (h' ≫ f') (g' ≫ f)
      ((h' ≫ g') ≫ f) rfl sq₁.w (by rw [Category.assoc, sq₁.w, Category.assoc]),
    map_comp_hom_comp_inv A h' g' f (h' ≫ g') (g' ≫ f)
      ((h' ≫ g') ≫ f) rfl rfl rfl, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

private lemma comparison_vert
    {X Y X' Y' W W' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
    (sq₁ : CommSq g' f' f g) (sq₃ : CommSq g'' e' e g')
    (sq : CommSq g'' (e' ≫ f') (e ≫ f) g)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (upperStarCompDerivedPlus A e' f').symm.hom.app
        ((upperStar A g).mapDerivedCategoryPlus.obj K) ≫
      (pullbackSquareComparison A sq).hom.app K =
        (upperStar A e').mapDerivedCategoryPlus.map
          ((pullbackSquareComparison A sq₁).hom.app K) ≫
        (pullbackSquareComparison A sq₃).hom.app
            ((upperStar A f).mapDerivedCategoryPlus.obj K) ≫
        (upperStar A g'').mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus A e f).symm.hom.app K) := by
  apply (cancel_component_inverse (upperStarCompDerivedPlus A e' f')
    ((upperStar A g).mapDerivedCategoryPlus.obj K) _ _).mpr
  simp only [pullbackSquareComparison_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [comp_hom_map_comp_inv_assoc A e' f' g (e' ≫ f') (g' ≫ f)
      (g'' ≫ (e ≫ f)) rfl sq₁.w sq.w,
    map_comp_hom_comp_inv_assoc A e' g' f (g'' ≫ e) (g' ≫ f)
      (g'' ≫ (e ≫ f)) sq₃.w rfl (Category.assoc g'' e f).symm,
    comp_hom_map_comp_inv A g'' e f (g'' ≫ e) (e ≫ f)
      (g'' ≫ (e ≫ f)) rfl rfl (Category.assoc g'' e f).symm,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

private lemma comparison_laws :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (pullbackSquareComparison A (IsPullback.id_horiz f).toCommSq).hom.app K =
        (upperStar A f).mapDerivedCategoryPlus.map ((upperStarIdDerivedPlus A Y).hom.app K) ≫
          (upperStarIdDerivedPlus A X).inv.app
            ((upperStar A f).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {X Y X' Y' X'' Y'' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (upperStar A f'').mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus A h g).inv.app K) ≫
          (pullbackSquareComparison A (sq₂.paste_horiz sq₁).toCommSq).hom.app K =
        (pullbackSquareComparison A sq₂.toCommSq).hom.app
            ((upperStar A g).mapDerivedCategoryPlus.obj K) ≫
          (upperStar A h').mapDerivedCategoryPlus.map
            ((pullbackSquareComparison A sq₁.toCommSq).hom.app K) ≫
          (upperStarCompDerivedPlus A h' g').inv.app
            ((upperStar A f).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {X Y X' Y' W W' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
        (sq₁ : IsPullback g' f' f g) (sq₃ : IsPullback g'' e' e g')
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (upperStarCompDerivedPlus A e' f').inv.app
          ((upperStar A g).mapDerivedCategoryPlus.obj K) ≫
          (pullbackSquareComparison A (sq₃.paste_vert sq₁).toCommSq).hom.app K =
        (upperStar A e').mapDerivedCategoryPlus.map
            ((pullbackSquareComparison A sq₁.toCommSq).hom.app K) ≫
          (pullbackSquareComparison A sq₃.toCommSq).hom.app
            ((upperStar A f).mapDerivedCategoryPlus.obj K) ≫
          (upperStar A g'').mapDerivedCategoryPlus.map
            ((upperStarCompDerivedPlus A e f).inv.app K)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y f K
    exact comparison_id A f K
  · intro X Y X' Y' X'' Y'' f f' g g' f'' h h' sq₁ sq₂ K
    exact comparison_horiz A sq₁.toCommSq sq₂.toCommSq (sq₂.paste_horiz sq₁).toCommSq K
  · intro X Y X' Y' W W' f f' g g' e e' g'' sq₁ sq₃ K
    exact comparison_vert A sq₁.toCommSq sq₃.toCommSq (sq₃.paste_vert sq₁).toCommSq K

end

/-- Identity, horizontal pasting and vertical pasting of derived square comparisons.
Source: Stacks Project, Remarks 0E46 and 0E47
(blueprint: lem-weil-pbc-derived-square-iso-pasting).

Proof: Express each square comparison as the inverse composition comparison for
one path followed by the composition comparison for the other path. For the identity
square, choose the diagonal to be f and use the two derived unit laws. For horizontal
pasting, use derived associativity on (f'', h, g), (h', f', g), and (h', g', f).
For vertical pasting, use it on (e', f', g), (e', g', f), and (g'', e, f).
The intermediate composition maps cancel. Finally cancel the source composition
comparison to obtain precisely the displayed equations. The argument works for every
commutative square and every Grothendieck abelian coefficient category, and is
specialized here to abelian groups. No further localization argument is needed -/
theorem derivedSquareIsoPasting :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})),
      (pullbackSquareComparison AddCommGrpCat.{u + 1} (IsPullback.id_horiz f).toCommSq).hom.app K =
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.map
          ((upperStarIdDerivedPlus AddCommGrpCat.{u + 1} Y).hom.app K) ≫
          (upperStarIdDerivedPlus AddCommGrpCat.{u + 1} X).inv.app
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {X Y X' Y' X'' Y'' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})),
      (upperStar AddCommGrpCat.{u + 1} f'').mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h g).inv.app K) ≫
          (pullbackSquareComparison AddCommGrpCat.{u + 1}
            (sq₂.paste_horiz sq₁).toCommSq).hom.app K =
        (pullbackSquareComparison AddCommGrpCat.{u + 1} sq₂.toCommSq).hom.app
            ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj K) ≫
          (upperStar AddCommGrpCat.{u + 1} h').mapDerivedCategoryPlus.map
            ((pullbackSquareComparison AddCommGrpCat.{u + 1} sq₁.toCommSq).hom.app K) ≫
          (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h' g').inv.app
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {X Y X' Y' W W' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
        (sq₁ : IsPullback g' f' f g) (sq₃ : IsPullback g'' e' e g')
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})),
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e' f').inv.app
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj K) ≫
          (pullbackSquareComparison AddCommGrpCat.{u + 1}
            (sq₃.paste_vert sq₁).toCommSq).hom.app K =
        (upperStar AddCommGrpCat.{u + 1} e').mapDerivedCategoryPlus.map
            ((pullbackSquareComparison AddCommGrpCat.{u + 1} sq₁.toCommSq).hom.app K) ≫
          (pullbackSquareComparison AddCommGrpCat.{u + 1} sq₃.toCommSq).hom.app
            ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K) ≫
          (upperStar AddCommGrpCat.{u + 1} g'').mapDerivedCategoryPlus.map
            ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e f).inv.app K)) := by
  exact comparison_laws AddCommGrpCat.{u + 1}

end AlgebraicGeometry.Etale
