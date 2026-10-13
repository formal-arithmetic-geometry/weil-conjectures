/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Finite raw section lifts

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-sections-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the raw section presentation and finite-stage construction.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-sections-lift).

Proof: Evaluation preserves the outer presheaf colimit, so each of the finitely
many given elements has a representative in some B(t). The pointwise Kan formula
represents it by a section at Z and an arrow from V(j)(Y(p)) to V(t)(Z).
Lift that arrow and its endpoint equalities using the arrow and object set colimits.
Move to a stage receiving j and t.right, and equalize the two maps from i so that
it is an object of Under i receiving t. Transport the section by theta and restrict
along the lifted arrow. Naturality of beta, the colimit coprojections and h-beta-map
identify its raw image with the given element transported along the cocone equality.
The unit condition identifies theta with the unique adjunction transpose, so these
transports compose. Filteredness gives a common refinement for the finite list of
representatives and equalizes the finitely many arrows from j. At this refinement
all elements are represented at F(a)(Y(p)). The cocone equation gives e for every
object of F(j). If the index is empty, take any common successor of i and j and the
empty family. No compatibility, covering family, or amalgamation is involved.
-/
theorem colimit_site_raw_finite_sections_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
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
    (j : J) (I : Type u) [Finite I] (Y : I → F.obj j)
    (x : ∀ p, (colimit B).obj (op ((V.ι.app j).toFunctor.obj (Y p)))) :
    ∃ (t : Under i) (a : j ⟶ t.right)
      (e : ∀ U : F.obj j,
        (V.ι.app t.right).toFunctor.obj ((F.map a).toFunctor.obj U) =
          (V.ι.app j).toFunctor.obj U)
      (s : ∀ p, ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map a).toFunctor.obj (Y p)))),
      ∀ p, (colimit.ι B t).app
        (op ((V.ι.app t.right).toFunctor.obj ((F.map a).toFunctor.obj (Y p))))
        ((β t).app (op ((F.map a).toFunctor.obj (Y p))) (s p)) =
      (colimit B).map (eqToHom (e (Y p))).op (x p) := by sorry

end CategoryTheory
