/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.CategoryTheory.ColimitSiteAbelianStageImage
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Nonempty-cover reduction for finite family stabilization.
Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-abelian-finite-family-stabilization-nonempty)
-/
theorem colimit_site_abelian_finite_family_stabilization_nonempty
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
    (hTnonempty : Nonempty T.uncurry)
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
                ((α t).hom.app (op Z) (y g hg)) := by sorry

end CategoryTheory
