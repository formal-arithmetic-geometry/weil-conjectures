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
        (upperStarIdDerivedPlus A X).inv.app ((upperStar A f).mapDerivedCategoryPlus.obj K) := by
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
    (pullbackSquareComparison A sq).hom.app K =
      (upperStar A f'').mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus A h g).hom.app K) ≫
        (pullbackSquareComparison A sq₂).hom.app ((upperStar A g).mapDerivedCategoryPlus.obj K) ≫
        (upperStar A h').mapDerivedCategoryPlus.map
          ((pullbackSquareComparison A sq₁).hom.app K) ≫
        (upperStarCompDerivedPlus A h' g').inv.app
          ((upperStar A f).mapDerivedCategoryPlus.obj K) := by
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
    (pullbackSquareComparison A sq).hom.app K =
      (upperStarCompDerivedPlus A e' f').hom.app
          ((upperStar A g).mapDerivedCategoryPlus.obj K) ≫
        (upperStar A e').mapDerivedCategoryPlus.map
          ((pullbackSquareComparison A sq₁).hom.app K) ≫
        (pullbackSquareComparison A sq₃).hom.app ((upperStar A f).mapDerivedCategoryPlus.obj K) ≫
        (upperStar A g'').mapDerivedCategoryPlus.map
          ((upperStarCompDerivedPlus A e f).inv.app K) := by
  simp only [pullbackSquareComparison_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [comp_hom_map_comp_inv_assoc A e' f' g (e' ≫ f') (g' ≫ f)
      (g'' ≫ (e ≫ f)) rfl sq₁.w sq.w,
    map_comp_hom_comp_inv_assoc A e' g' f (g'' ≫ e) (g' ≫ f)
      (g'' ≫ (e ≫ f)) sq₃.w rfl (Category.assoc g'' e f).symm,
    comp_hom_map_comp_inv A g'' e f (g'' ≫ e) (e ≫ f)
      (g'' ≫ (e ≫ f)) rfl rfl (Category.assoc g'' e f).symm,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

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
    let A := AddCommGrpCat.{u + 1}
    let P := fun {S T : Scheme.{u}} (q : S ⟶ T) => (upperStar A q).mapDerivedCategoryPlus
    let θ := fun {S T S' T' : Scheme.{u}} {a : S' ⟶ S} {b : S' ⟶ T'}
        {c : S ⟶ T} {d : T' ⟶ T} (sq : CommSq a b c d) => pullbackSquareComparison A sq
    let c := fun {R S T : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) =>
      (upperStarCompDerivedPlus A a b).symm
    let i := fun S : Scheme.{u} => upperStarIdDerivedPlus A S
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (θ (IsPullback.id_horiz f).toCommSq).hom.app K =
        (P f).map ((i Y).hom.app K) ≫ (i X).inv.app ((P f).obj K)) ∧
    (∀ {X Y X' Y' X'' Y'' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {f'' : X'' ⟶ Y''} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
        (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (P f'').map ((c h g).hom.app K) ≫
          (θ (sq₂.paste_horiz sq₁).toCommSq).hom.app K =
        (θ sq₂.toCommSq).hom.app ((P g).obj K) ≫
          (P h').map ((θ sq₁.toCommSq).hom.app K) ≫
          (c h' g').hom.app ((P f).obj K)) ∧
    (∀ {X Y X' Y' W W' : Scheme.{u}}
        {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
        {e : W ⟶ X} {e' : W' ⟶ X'} {g'' : W' ⟶ W}
        (sq₁ : IsPullback g' f' f g) (sq₃ : IsPullback g'' e' e g')
        (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)),
      (c e' f').hom.app ((P g).obj K) ≫
          (θ (sq₃.paste_vert sq₁).toCommSq).hom.app K =
        (P e').map ((θ sq₁.toCommSq).hom.app K) ≫
          (θ sq₃.toCommSq).hom.app ((P f).obj K) ≫
          (P g'').map ((c e f).hom.app K)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro X Y f K
    exact comparison_id AddCommGrpCat.{u + 1} f K
  · intro X Y X' Y' X'' Y'' f f' g g' f'' h h' sq₁ sq₂ K
    rw [comparison_horiz AddCommGrpCat.{u + 1} sq₁.toCommSq sq₂.toCommSq]
    simp only [Iso.symm_hom, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  · intro X Y X' Y' W W' f f' g g' e e' g'' sq₁ sq₃ K
    rw [comparison_vert AddCommGrpCat.{u + 1} sq₁.toCommSq sq₃.toCommSq]
    simp only [Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp]

end AlgebraicGeometry.Etale
