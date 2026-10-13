/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups F1 and M2
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # ColimitSiteRawAbelianSectionEvaluation

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs; abelian colimits
as in Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-raw-abelian-section-evaluation).

Proof: Construct R as the chosen abelian colimit cocone of D. Put Y = V_i(U).
For each t the cocone equation gives e_t : V_t(F(t.hom)(U)) = Y. Compose E_t,
the component of β_t, the coprojection into colimit B and the transport along
e_t. The equations hm and hβmap and naturality of the coprojections prove that
these maps are a cocone. Hence they induce μ : R.pt → (colimit B)(Y).

Construct an inverse by the pointwise Kan formula. An abelian Kan generator is
(W, x, f : Y → V_t(W)). Lift f and both endpoints to a stage receiving i and
t.right using the object and arrow set-colimit hypotheses. Refine further to
align the endpoints with the prescribed images, and equalize the arrows out
of i so the refinement is an arrow b : t → t' in Under i. Apply θ_b to x,
restrict along the lifted f, apply E_t' inverse, and take the coprojection of D.
Extend this map additively to finite sums of generators. Two choices of stage,
endpoint or arrow lifts agree at a further common refinement by eventual
object and arrow equality; naturality of θ and hm then give the same D class.
Linearity relations are respected by additivity. For a Kan restriction relation
lift its defining triangle to one stage and use presheaf naturality. Transition
relations are respected by hβmap and hm. Every relation in the abelian colimit
is a finite sum of these relations, so filteredness supplies one common stage.
The additive assignment therefore descends to an inverse ψ of μ.

On a D generator choose its own stage and the identity restriction: ψμ is the
identity by the defining section maps. On a Kan generator the lifted restriction
is a Kan relation, so naturality of β and hβmap prove μψ is the identity. Thus
q is the isomorphism with hom μ; no arbitrary witness is used for R or q.
Compose the coprojection formula for q with colimit.desc B γ. Naturality moves
the endpoint transport to T, colimit.ι_desc_app replaces the coprojection by γ_t,
and ha replaces β_t followed by γ_t by a_t. Arrow equality removes the endpoint
transport and yields the stated formula. No finiteness of covers, sheaf condition
on T or colimit B, or equality in the canonical inverse image is assumed.
-/
theorem colimit_site_raw_abelian_section_evaluation
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
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (U : F.obj i)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (T : V.ptᵒᵖ ⥤ AddCommGrpCat.{u})
    (γ : B ⟶ (Functor.const (Under i)).obj T)
    (a : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ T)
    (ha : ∀ (t : Under i) (X : F.obj t.right),
      (β t).app (op X) ≫
        (γ.app t).app (op ((V.ι.app t.right).toFunctor.obj X)) = (a t).app (op X))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) :
    ∃ (R : Cocone D)
      (q : R.pt ≅ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U))),
      Nonempty (IsColimit R) ∧
      ∀ t : Under i,
        Arrow.mk (R.ι.app t ≫ q.hom ≫
          (colimit.desc B (Cocone.mk T γ)).app
            (op ((V.ι.app i).toFunctor.obj U))) =
        Arrow.mk ((E t).hom ≫ (a t).app (op ((F.map t.hom).toFunctor.obj U))) := by sorry

end CategoryTheory
