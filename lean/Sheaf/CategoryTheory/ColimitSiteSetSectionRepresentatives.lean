/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Every limit inverse-image section is represented by a stage section.

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-section-representatives).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-set-section-representatives).

Every limit inverse-image section is represented by a stage section.

Proof: For each limit-site object Y, take presentations (a : i to j, W in
F j, V j W = Y). Object-colimit representatives give a presentation above i.
Filteredness and eventual equality of object and arrow representatives give
common refinements and equalizers, hence a filtered presentation category.
Take the colimit of sections of the stage inverse images at W. Restriction
arrows lift to a common stage; eventual equality makes their maps independent
of the lift and gives identity and composition. Every Q-cover lifts by hQ to
a finite stage cover. Covering pullbacks are preserved, so its matching-family
equalizer is the filtered colimit of the stage sheaf equalizers. Filtered
colimits commute with finite products and equalizers, also empty products;
thus this presheaf is a sheaf. A map from it to H is a compatible family of
stage maps. Transposing by the stage adjunctions identifies this family with
one map G to restriction of H along V i; conversely transpose that map at every
presentation. The identity presentation and uniqueness of adjuncts prove the
two operations inverse. The unit-compatible left-adjoint isomorphism therefore
identifies the constructed sheaf with the limit inverse image. At V i U the
presentations arising from U are final: any presentation and a map to V i U
lift together at a stage, and two lifts agree after refinement by the object
and arrow colimit criteria. Every element of this filtered set colimit has a
representative from Under i. Its image is the specified α by uniqueness under
hα. Transfer it through E and the isomorphism e using hι to obtain y and the
asserted equality x = K.ι.app t y. This proves only existence of representatives,
not their equality criterion or any diagram laws.
-/
theorem colimit_site_set_section_representatives
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
    (U : F.obj i)
    (D : Under i ⥤ Type u)
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (K : Cocone D)
    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
          (op ((V.ι.app i).toFunctor.obj U)))
    (hι : ∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))):
    ∀ x : K.pt, ∃ (t : Under i) (y : D.obj t), x = K.ι.app t y := by sorry

end CategoryTheory
