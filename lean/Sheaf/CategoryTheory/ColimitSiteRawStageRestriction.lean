/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Stage restriction of the raw Kan colimit

Source: Stacks Project, Sites, Tag 0A35, section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-stage-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The restriction of the raw presheaf to any stage is a filtered presheaf colimit
of stage sheaves. This comparison uses no finiteness assumption on covering presieves.
Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-stage-restriction).

Proof: Choose a common stage k receiving i and j by filteredness, with arrows a and b.
For t in Under k, pull G to t.right along a followed by t.hom, and push this sheaf
back to stage j along b followed by t.hom. These are the objects D(t). Along a
morphism of Under k, use the adjunction transpose of the unit to define the
transition. Uniqueness of adjunction transposes proves the identity and composition
laws. The hypothesis htheta identifies these transitions with the supplied theta.

At an object U of stage j, the Kan unit beta followed by the outer coprojection
maps a section of D(t) to the raw colimit at V(j)(U), using the cocone equality to
identify V(t.right)(F(b followed by t.hom)(U)) with V(j)(U). Naturality of beta,
hbeta_map, and the coprojection equations make these maps a cocone and natural in U.
Every Kan generator at V(j)(U) is a stage section paired with an arrow from V(j)(U)
to a stage image. Represent that arrow and its endpoints in the object and arrow
set colimits, move to a stage receiving k and the generator's stage, and equalize
the arrows from k. Restriction along the lifted arrow gives a D representative.
Thus the induced comparison is surjective. Any equality of generators is a finite
chain of Kan and outer-colimit relations. Lift all arrows and equations in this
chain to one later stage, using the filtered-set eventual-equality criterion.
Naturality and hbeta_map identify each relation with a section restriction or the
transition of D. Therefore the two D representatives agree at a further stage,
proving injectivity. These inverse bijections are natural in U, and define the
presheaf isomorphism q. The specified object isomorphisms are identities for this
construction. No finite cover, amalgamation, or separatedness is used here.
-/
theorem colimit_site_raw_stage_restriction
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
    (j : J) :
    ∃ (k : J) (a : i ⟶ k) (b : j ⟶ k)
      (D : Under k ⥤ Sheaf (P j).toGrothendieck (Type u)),
      Nonempty (colimit (D ⋙ sheafToPresheaf (P j).toGrothendieck (Type u)) ≅
        (V.ι.app j).toFunctor.op ⋙ colimit B) ∧
      ∀ t : Under k, Nonempty (D.obj t ≅
        ((F.map (b ≫ t.hom)).toFunctor.sheafPushforwardContinuous (Type u)
          (P j).toGrothendieck (P t.right).toGrothendieck).obj
          ((sheafPullback (F.map (a ≫ t.hom)).toFunctor (Type u)
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G)) := by sorry

end CategoryTheory
