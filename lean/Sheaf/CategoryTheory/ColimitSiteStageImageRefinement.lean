/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.ColimitSiteStageImage

/-! # ColimitSiteStageImageRefinement

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-stage-image-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-stage-image-refinement).

Proof: Unpack membership as a stage t, an object W, a presenting arrow
f : V i U to V t W, and a section z at W. Lift this finite diagram to a
common stage above i and t using the object and arrow colimit hypotheses.
Eventual object equality identifies its endpoints with the images of U and W;
eventual arrow equality makes the lifted arrow represent f. Transport z by
the adjunction transpose of the later unit, then restrict along this lifted
arrow. This gives a section at the later image of U. The two composites to
the limit restriction sheaf have equal transposes by the unit equations hα
and the cocone equation for V. Injectivity of the adjunction hom equivalence
therefore identifies them. Naturality applied to the lifted arrow says that
the resulting section has image the given restriction of alpha t z.
This concerns an already presented section, not an arbitrary limit section.
-/
theorem colimit_site_stage_image_refinement
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
    (x : ((sheafPullback (V.ι.app i).toFunctor (Type u)
      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op ((V.ι.app i).toFunctor.obj U)))
    (hx : x ∈ (colimitSiteStageImage F P V Q i G α).obj
      (op ((V.ι.app i).toFunctor.obj U))) :
    ∃ (t : Under i)
      (z : ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
        (op ((F.map t.hom).toFunctor.obj U))),
      HEq ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) z) x := by sorry

end CategoryTheory
