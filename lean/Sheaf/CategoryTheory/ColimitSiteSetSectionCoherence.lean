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

/-! # Unit-compatible section maps satisfy the functor and cocone laws.

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-section-coherence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-set-section-coherence).

Unit-compatible section maps satisfy the functor and cocone laws.

Proof: The equalities of functors supplied by F.map_id, F.map_comp, Under.w,
and V.w identify all composite restriction functors. For each transition, the
adjunction hom equivalence sends a sheaf map to its composite with the unit.
Consequently the componentwise unit equations hθ determine the transition
uniquely: equality of components gives equality of natural transformations,
and injectivity of the hom equivalence gives equality of sheaf maps. The
identity sheaf map satisfies the identity unit equation. A composite of two
transitions satisfies the composite unit equation, by naturality of the units
and of the second transition. Uniqueness therefore proves identity and
composition. Likewise, the composite of a transition with the later α has
unit composite equal to the limit-site unit by hθ and hα, so equals the earlier
α. Evaluate these three sheaf-map equalities at the image of U. The Arrow
identities hm and hc identify m and c with these evaluated maps, after the
endpoint transports forced by the functor equalities. Transport respects
identities and composition, giving the three stated laws. No filteredness,
covering finiteness, or category-colimit hypothesis is needed.
-/
theorem colimit_site_set_section_coherence
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
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
    (U : F.obj i)
    (m : ∀ (t t' : Under i) (b : t ⟶ t'), ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)) ⟶ ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t'.hom).toFunctor.obj U)))
    (c : ∀ t : Under i, ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)) ⟶ ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
          (op ((V.ι.app i).toFunctor.obj U)))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk (m t t' b) =
        Arrow.mk ((θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))))
    (hc : ∀ t : Under i,
      Arrow.mk (c t) =
        Arrow.mk ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) :
    (∀ t : Under i, m t t (𝟙 t) = 𝟙 _) ∧
    (∀ (t t' t'' : Under i) (b : t ⟶ t') (b' : t' ⟶ t''),
      m t t'' (b ≫ b') = m t t' b ≫ m t' t'' b') ∧
    (∀ (t t' : Under i) (b : t ⟶ t'), m t t' b ≫ c t' = c t) := by sorry

end CategoryTheory
