/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic

import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionDiagram
import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionUniversality
import WeilConjectures.CategoryTheory.FilteredColimitCategories

/-! # A step in the filtered colimit site construction.

Source: Stacks Project, Sites, Tags 09YL and 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem sheaf_triangle_unit
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{u}) :
    ∃ α : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
        ((sheafPullback h AddCommGrpCat.{u} T R).obj G),
      ∀ X : C,
        Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
          (op X) ≫ α.hom.app (op (f.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
          (op X)) := by
  subst h
  let adj := sheafAdjunctionContinuous f AddCommGrpCat.{u} T S
  let H := (sheafPullback (f ⋙ g) AddCommGrpCat.{u} T R).obj G
  let η := (sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} T R).unit.app G
  let β : G ⟶ (f.sheafPushforwardContinuous AddCommGrpCat.{u} T S).obj
      ((g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj H) := ⟨η.hom⟩
  refine ⟨(adj.homEquiv G _).symm β, ?_⟩
  intro X
  have eq := (adj.homEquiv G _).apply_symm_apply β
  have eq' := congrArg (fun k ↦ k.hom.app (op X)) eq
  exact congrArg Arrow.mk eq'

/-- For a filtered colimit of finitary sites with colimit precoverage `Q`, the inverse image of
an abelian sheaf `G` from stage `i` to the colimit site has, over the image of `U`, the filtered
colimit over `Under i` of the sections of the inverse images of `G` to the later stages, with
coprojections and transition maps compatible with the units of the adjunctions.

Source: Stacks Project, Sites, Tag 0A35, the presentation construction and adjunction argument;
the abelian extension uses Sites, Modules, Tag 03CO. -/
theorem colimit_site_abelian_inverse_image
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck] :
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u}),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ AddCommGrpCat.{u})
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) := by
  classical
  intro i G
  have ha : ∀ t : Under i, ∃ a : (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
    i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G), ∀ X : F.obj i,
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ a.hom.app (op
        ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)) := by
    intro t
    exact sheaf_triangle_unit (P i).toGrothendieck (P t.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor (V.ι.app i).toFunctor
      (congrArg Cat.Hom.toFunctor (V.w t.hom)) G
  choose α hα using ha
  have ht : ∀ (t t' : Under i) (b : t ⟶ t'), ∃ a :
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶ ((F.map b.right).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G),
      ∀ X : F.obj i,
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ a.hom.app (op
        ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)) := by
    intro t t' b
    apply sheaf_triangle_unit (P i).toGrothendieck (P t.right).toGrothendieck (P
      t'.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map t'.hom).toFunctor _ G
    change (F.map t.hom ≫ F.map b.right).toFunctor = (F.map t'.hom).toFunctor
    rw [← F.map_comp, Under.w b]
  choose θ hθ using ht
  refine ⟨α, hα, ?_⟩
  intro U
  obtain ⟨D, E, K, e, hK, hD⟩ :=
    colimit_site_abelian_section_diagram J F P V Q i G α θ hα hθ U
  have hc := colimit_site_abelian_section_universality J F P hfinite hcover hpullback
    V hobjects harrows Q hQ hVpullback i G α θ hα hθ U D E K e hK hD
  refine ⟨D, E, K, e, hc, hK, ?_⟩
  intro t t' b
  exact ⟨θ t t' b, hθ t t' b, hD t t' b⟩

end CategoryTheory
