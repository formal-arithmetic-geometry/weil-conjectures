/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Finite raw overlap refinement

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-matching-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the finite overlap-equation calculation before stage gluing.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-matching-refinement).

Proof: Take the pairwise covering pullbacks at the given stage. Naturality of beta
and the coprojections identifies the raw images of the two restricted sections.
The assumed raw compatibility makes them equal. The pointwise Kan presentation,
with object and arrow set colimits, detects equality of stage sections after a
transition: lift the finite chain of Kan and outer colimit relations to one stage,
where naturality and h-beta-map turn them into restriction and theta transport.
The unit condition h-theta makes theta the unique adjunction transpose and hence
makes these transports compose. There are finitely many pairs of covering arrows;
filteredness and equalization give one transition where every equality holds.
Transition preservation of covering pullbacks identifies the transported equations
with equations on pairwise pullbacks at the new stage. The pullback universal
property proves indexed compatibility on arbitrary common test objects. Transport
the original sections by theta to obtain s'. Naturality and h-beta-map give the
stated equality of raw images; e is the cocone equality. Repeated arrows therefore
have equal sections, including after transport. For an empty family use the identity
transition and the empty family. No new raw representatives or amalgamation are needed.
-/
theorem colimit_site_raw_finite_matching_refinement
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasPullbacks]
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
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (t : Under i) (W : F.obj t.right) (I : Type u) [Finite I]
    (Y : I → F.obj t.right) (f : ∀ p, Y p ⟶ W)
    (hf : Presieve.ofArrows Y f ∈ P t.right W)
    (s : ∀ p, ((sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op (Y p)))
    (hs : Presieve.Arrows.Compatible ((V.ι.app t.right).toFunctor.op ⋙ colimit B) f
      (fun p ↦ (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (Y p)))
        ((β t).app (op (Y p)) (s p)))) :
    ∃ (t' : Under i) (b : t ⟶ t')
      (e : ∀ U : F.obj t.right,
        (V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj U) =
          (V.ι.app t.right).toFunctor.obj U)
      (s' : ∀ p, ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj
          (op ((F.map b.right).toFunctor.obj (Y p)))),
      Presieve.Arrows.Compatible
        ((sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj
        (fun p ↦ (F.map b.right).toFunctor.map (f p)) s' ∧
      ∀ p, (colimit.ι B t').app
        (op ((V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj (Y p))))
        ((β t').app (op ((F.map b.right).toFunctor.obj (Y p))) (s' p)) =
      (colimit B).map (eqToHom (e (Y p))).op
        ((colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (Y p)))
          ((β t).app (op (Y p)) (s p))) := by sorry

end CategoryTheory
