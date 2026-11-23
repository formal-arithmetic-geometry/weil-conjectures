/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import WeilConjectures.CategoryTheory.ColimitSiteAbelianFiniteFamilyStabilizationNonempty

/-! # Stabilization of finite abelian stage families

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A finite stage family whose alpha images match becomes matching after refinement.
Source: Stacks Project, Sites, Tag 0A35 matching equalizer
paragraph and the adjunction paragraph; Modules on Sites, Tag 03CO. -/
theorem colimit_site_abelian_finite_family_stabilization
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
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (t : Under i) (W : F.obj t.right) (T : Presieve W) (hT : T ∈ P t.right W)
    (y : T.FamilyOfElements
      (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
          forget AddCommGrpCat.{u}))
    (hy : (show T.FamilyOfElements
        ((V.ι.app t.right).toFunctor.op ⋙
          (ColimitSiteStageImage.target F P V Q i G).obj ⋙ forget AddCommGrpCat.{u}) from
        fun {Z} g hg ↦ (α t).hom.app (op Z) (y g hg)).Compatible) :
    ∃ (t' : Under i) (W' : F.obj t'.right) (T' : Presieve W'), T' ∈ P t'.right W' ∧
      ∃ (hW : (V.ι.app t'.right).toFunctor.obj W' = (V.ι.app t.right).toFunctor.obj W)
        (y' : T'.FamilyOfElements
          (((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj ⋙
              forget AddCommGrpCat.{u})),
        y'.Compatible ∧ ∀ {Z' : F.obj t'.right} (g' : Z' ⟶ W') (hg' : T' g'),
          ∃ (Z : F.obj t.right) (g : Z ⟶ W) (hg : T g)
            (r : (V.ι.app t'.right).toFunctor.obj Z' ⟶ (V.ι.app t.right).toFunctor.obj Z),
            (V.ι.app t'.right).toFunctor.map g' ≫ eqToHom hW =
              r ≫ (V.ι.app t.right).toFunctor.map g ∧
            (α t').hom.app (op Z') (y' g' hg') =
              (ColimitSiteStageImage.target F P V Q i G).obj.map r.op
                ((α t).hom.app (op Z) (y g hg)) := by
  classical
  by_cases hne : Nonempty T.uncurry
  · exact colimit_site_abelian_finite_family_stabilization_nonempty
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
      i G α hα t W T hT hne y hy
  · let y0 := y
    have hy0 : y0.Compatible := by
      intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
      exact False.elim (hne ⟨⟨Z₁, f₁⟩, hf₁⟩)
    refine ⟨t, W, T, hT, rfl, y0, hy0, ?_⟩
    intro Z g hg
    exact False.elim (hne ⟨⟨Z, g⟩, hg⟩)

end CategoryTheory
