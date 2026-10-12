/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.CategoryTheory.ColimitSiteAbelianStageImage
public import Sheaf.CategoryTheory.ArrowsFunctor

/-! # Individual stage lifts on a finite cover

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Finite covering families of generated sections have individual stage lifts.
Source: Stacks Project, Sites, Tag 0A35, the general-object presentation and
finite-cover paragraph; Modules on Sites, Tag 03CO, for abelian coefficients.
(blueprint: lem-weil-pbc-colimit-site-abelian-cover-section-lift).

Proof: Write the Q-cover R as the transported image of a stage cover using hQ.
Its stage presieve is finite by hfinite. Move that stage above i by filteredness,
transporting the cover by hcover. For each of its finitely many arrows, expand
membership of the corresponding section in the generated subgroup as a finite
additive expression in restrictions of stage images. Lift each restriction arrow
using the arrow colimit and align its endpoints using eventual equality in the
object colimit. Move the finitely many stages and endpoint equations to a common
stage above the cover. The transition of each inverse image is the transpose of
the direct unit under the preceding stage adjunction. Uniqueness of adjuncts and
h-alpha show that alpha after this transition equals the old alpha. Naturality
therefore gives a representative of every generating restriction. Add and negate
these representatives to lift the finite additive expressions. Further transitions
retain these image formulas by the same unit argument. Take the transported stage
cover. If different original arrows become equal, choose one lift for each actual
arrow of the transported presieve; their target sections are identical, since
both are the value of x on the same image arrow. Thus the choices still satisfy
the stated image equation. This gives a family of individual lifts, with no
compatibility conclusion. For an empty cover take its empty transported family;
there are no section choices or equations. No sheaf amalgamation is used.
-/
theorem colimit_site_abelian_cover_section_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
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
    (Y : V.pt) (R : Presieve Y) (hR : R ∈ Q Y)
    (x : R.FamilyOfElements
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u})) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W), T ∈ P t.right W ∧
      ∃ (hY : (V.ι.app t.right).toFunctor.obj W = Y)
        (hTR : ∀ {Z : F.obj t.right} (g : Z ⟶ W), T g →
          R ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY))
        (y : T.FamilyOfElements
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
              forget AddCommGrpCat.{u})),
        ∀ {Z : F.obj t.right} (g : Z ⟶ W) (hg : T g),
          (α t).hom.app (op Z) (y g hg) =
            (x ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) (hTR g hg)).val := by sorry

end CategoryTheory
