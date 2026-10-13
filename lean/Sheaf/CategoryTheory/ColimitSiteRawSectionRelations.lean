/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Eventual equality for the raw Kan section colimit

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction, independence of the presentation and restriction arrows.
(blueprint: lem-weil-pbc-colimit-site-raw-section-relations).

Proof: First the adjunction hom-equivalence and htheta determine theta_b
uniquely: its adjoint is the unit at t' after the canonical functor transports.
Injectivity of this hom-equivalence gives theta_id = id and compatibility of
theta with composition, with the same transports. Thus sections can be moved
through successive refinements without changing their eventual value.

Evaluate the outer presheaf colimit at Y = V_i(U). Its filtered-set equality
criterion moves the two given representatives to B_k(Y) for a common object
k of Under i. The equations hbeta_map, hm and hkappa identify them with the
beta_k unit representatives of their transported sections at U_k = F(k.hom)(U).
The pointwise left Kan formula identifies B_k(Y) with the set colimit whose
generators are triples (W, f, s), where W lies in F(k.right), f : Y -> V_k(W),
and s is a section at W. Equality of two generators in a set colimit means a
finite zigzag of generating relations. A relation from h : W -> W' identifies
(W, f, A_k.map(h.op)(s')) with (W', f followed by V_k(h), s').

Lift the finitely many f arrows to one later stage r, using surjectivity of
the arrow colimit. The object-colimit equality criterion aligns their sources
with U_r and their targets with the forward images of the W. Refine again so
the arrow-colimit equality criterion enforces every triangle from the zigzag
and makes the endpoint arrows the identities of U_r. Equalize the finitely
many competing stage maps, including those out of i, so all these choices
use one arrow k -> r in Under i. Finite repetition preserves all earlier
equations because the transition functors preserve equality and composition.

Send (W, f, s) to the section obtained by applying theta_(k,r) to s and
restricting along the chosen lift g : U_r -> F(k -> r)(W). Each generating
relation has equal images: naturality of theta moves restriction by h through
theta, and the lifted triangle identifies g followed by F(k -> r)(h) with
the next lifted arrow. Both orientations of a relation preserve equality, so
induction along the zigzag equates its endpoint sections. The identity
endpoint arrows and composition compatibility of theta identify these with
the sections obtained from the original x and x' at stage r. Finally hm and
the injectivity of (E r).hom give D.map b x = D.map b' x'. This proves only
the eventual equality criterion; no representative-existence or comparison
isomorphism is used.
-/
theorem raw_section_relations
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
    (U : F.obj i)
    (D : Under i ⥤ Type u)
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom))
    (κ : ∀ t : Under i,
      D.obj t ⟶ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)))
    (hκ : ∀ t : Under i,
        ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
            (V.ι.app i).toFunctor.obj U,
          κ t =
            (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
              (colimit.ι B t).app
                (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
              eqToHom (congrArg (fun X => (colimit B).obj (op X)) e)) :
    ∀ (t t' : Under i) (x : D.obj t) (x' : D.obj t'),
      κ t x = κ t' x' →
        ∃ (r : Under i) (b : t ⟶ r) (b' : t' ⟶ r), D.map b x = D.map b' x' := by sorry

end CategoryTheory
