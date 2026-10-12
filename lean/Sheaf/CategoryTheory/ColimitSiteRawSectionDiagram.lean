/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # ColimitSiteRawSectionDiagram

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-diagram).

Proof: Construct B(t) as the left Kan extension of the underlying stage inverse-image
sheaf along V(t.right).op, and β(t) as its universal unit. For b : t to t',
compose θ(b) with β(t') and transport along V.w; the Kan universal property
constructs B.map b. Adjunction uniqueness under hθ proves identities and
composition. Extend α(t) by the same Kan property to γ(t); hα and hθ prove
naturality. This constructs the raw diagram and its comparison maps only;
no sheaf condition or isomorphism after sheafification is asserted here.
The universal units determine B, its maps and γ up to the unique compatible
isomorphism; no arbitrary existence witness is used to define an object.
-/
theorem colimit_site_raw_section_diagram
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (Q : Precoverage V.pt)
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
 :
    ∃ (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
      (β : ∀ t : Under i,
        ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
      (γ : B ⟶ (Functor.const (Under i)).obj
        ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj),
      (∀ t : Under i, (B.obj t).IsLeftKanExtension (β t)) ∧
      (∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
        Arrow.mk ((β t).app (op X) ≫
          (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
        Arrow.mk ((θ t t' b).hom.app (op X) ≫
          (β t').app (op ((F.map b.right).toFunctor.obj X)))) ∧
      (∀ (t : Under i) (X : F.obj t.right),
        (β t).app (op X) ≫
          (γ.app t).app (op ((V.ι.app t.right).toFunctor.obj X)) =
        (α t).hom.app (op X)) := by sorry

end CategoryTheory
