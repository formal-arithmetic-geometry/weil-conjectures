/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.CategoryTheory.ColimitSiteAbelianStageImage
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage

/-! # Matching lifts of generated abelian sections

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A matching family of generated sections admits a matching lift on a stage cover.
Source: Stacks Project, Sites, Tag 0A35, the general-object presentation and finite-cover
paragraphs; Modules on Sites, Tag 03CO, for abelian coefficients.
(blueprint: lem-weil-pbc-colimit-site-abelian-stage-matching-lift).

Proof: Finite base change and composition, together with the finiteness of stage covers,
show that a covering sieve contains the image of a finite stage cover: sieves containing
such a cover form a topology, since base change preserves covers and transitivity
requires only finitely many further finite covers. Present its target
at a stage above i using the object colimit. Each of the finitely many local sections is
a finite additive expression in stage images and restrictions. Lift the objects and
restriction arrows to a common stage using the object and arrow colimits; eventual
object equality aligns their endpoints. Transpose the adjunction units to obtain the
transition maps. Uniqueness of adjuncts gives their composition laws and identifies
their composites with alpha by h-alpha. Thus the finitely many local expressions have
stage section representatives on a common transported cover.

To lift compatibility, compare the restrictions of these representatives to each
pairwise covering pullback. Their alpha images agree by compatibility of x and
naturality. Uniqueness of left adjoints identifies alpha with the cocone inverse-image
unit followed by the canonical composition isomorphism; hence their difference is
killed by that unit. Apply the existing finite source-unit zero-detection theorem to
the stage inverse image as a source sheaf and to each such difference. It gives a
transition whose unit kills the difference. The same composition isomorphism for
transition inverse images identifies this with equality after the canonical stage
transition. There are finitely many pairs of covering arrows; a common refinement
in the filtered under category makes all these equalities hold at once. Transition
functors preserve the covering pullbacks, so the transported family is pullback
compatible, hence compatible. Naturality and the unit equations preserve its alpha
images. An empty cover has no sections or compatibility equations to lift, and its
empty matching family is compatible. This asserts only a matching lift: amalgamation
and uniqueness are not part of the conclusion. No arbitrary witness defines an object.
-/
theorem colimit_site_abelian_stage_matching_lift
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
    (Y : V.pt) (S : Sieve Y) (hS : S ∈ Q.toGrothendieck Y)
    (x : S.arrows.FamilyOfElements
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u}))
    (hx : x.Compatible) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W), T ∈ P t.right W ∧
      ∃ (hY : (V.ι.app t.right).toFunctor.obj W = Y)
        (hTS : ∀ {Z : F.obj t.right} (g : Z ⟶ W), T g →
          S ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY))
        (y : T.FamilyOfElements
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
              forget AddCommGrpCat.{u})),
        y.Compatible ∧ ∀ {Z : F.obj t.right} (g : Z ⟶ W) (hg : T g),
          (α t).hom.app (op Z) (y g hg) =
            (x ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) (hTS g hg)).val := by sorry

end CategoryTheory
