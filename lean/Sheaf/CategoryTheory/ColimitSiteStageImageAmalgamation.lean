/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Sheaf.CategoryTheory.ColimitSiteStageImage

/-! Existence of stage-image amalgamations on finite mapped stage covers.
Source: Stacks Project, Sites, Tag 0A35.
(blueprint: aux-colimit-site-stage-image-cover-amalgamation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, the finite-cover equalizer argument.
(blueprint: aux-colimit-site-stage-image-cover-amalgamation).

Proof: The cover R is finite by hfinite. Choose stage presentations of its finitely
many section values using the definition of colimitSiteStageImage. Lift their
presenting objects and arrows, together with the cover, to one stage above i and j
using the object and arrow colimit hypotheses and filteredness. Stage adjunctions
identify the maps α with the canonical comparison maps: their composites with the
units agree by hα, and adjunction makes those composites determine the maps.
Equality in the limit inverse-image sheaf is locally equality of presheaf
representatives. The exact description hQ of covers, finite composition, and
hfinite let these local equalities be witnessed by finite stage covers. Lift
those witnesses to a common stage as well. Stage sheaf separatedness then makes
the finitely many matching equations hold on the pairwise covering pullbacks.
These pullbacks are preserved by hpullback and
hVpullback. Equivalently, use that filtered colimits commute with the finite
matching-family equalizer, as in Tag 0A35. The transported cover remains covering
by hcover. The sheaf at that stage therefore glues the family to a section z.
Its image under α, restricted along the presentation of the cover's target,
belongs to colimitSiteStageImage by construction and restricts to each value of x.
For the empty cover the equalizer is the terminal set; the stage sheaf supplies
its unique section by the same argument. Only existence on a mapped stage cover
is asserted here; uniqueness and passage to the generated topology are separate.
-/
theorem colimit_site_stage_image_cover_exists_amalgamation
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
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
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
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
    (j : J) (X : F.obj j) (R : Presieve X) (hR : R ∈ P j X)
    (x : (R.map (V.ι.app j).toFunctor).FamilyOfElements
      (colimitSiteStageImage F P V Q i G α).toFunctor) (hx : x.Compatible) :
    ∃ z, x.IsAmalgamation z := by sorry

end CategoryTheory
