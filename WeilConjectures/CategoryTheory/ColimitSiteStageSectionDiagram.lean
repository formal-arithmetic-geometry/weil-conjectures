/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.StageSectionTransitionExistence
import WeilConjectures.CategoryTheory.StageSectionFunctorFromTransitions


/-! # Functorial stage section diagrams

Source: Stacks Project, Sites, Tag 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The section diagram of the stage inverse images over `Under i`, evaluated at the image of
`U`, is functorial in the sheaf `G` and compatible with the unit-transposed transitions.
Stacks Project, Sites, Tag 0A35. -/
theorem colimit_site_stage_section_diagram
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (i : J) (U : F.obj i) :
    ∃ (L : Sheaf (P i).toGrothendieck (Type u) ⥤ (Under i ⥤ Type u))
      (E : ∀ t : Under i, L ⋙ (evaluation (Under i) (Type u)).obj t ≅
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⋙
          sheafToPresheaf (P t.right).toGrothendieck (Type u) ⋙
          (evaluation (F.obj t.right)ᵒᵖ (Type u)).obj
            (op ((F.map t.hom).toFunctor.obj U)))
      (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⟶
        sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck ⋙
          (F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
            (P t.right).toGrothendieck (P t'.right).toGrothendieck),
      (∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
        Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
            (op X) ≫ ((θ t t' b).app G).hom.app
              (op ((F.map t.hom).toFunctor.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app
            (op X))) ∧
      ∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t'),
        Arrow.mk ((E t).hom.app G ≫ ((θ t t' b).app G).hom.app
          (op ((F.map t.hom).toFunctor.obj U))) =
        Arrow.mk ((L.obj G).map b ≫ (E t').hom.app G) := by
  obtain ⟨θ, hθ⟩ := stage_section_transition_existence J F P i
  obtain ⟨L, E, hmL⟩ := stage_section_functor_from_transitions J F P i U θ hθ
  exact ⟨L, E, θ, hθ, hmL⟩

end CategoryTheory
