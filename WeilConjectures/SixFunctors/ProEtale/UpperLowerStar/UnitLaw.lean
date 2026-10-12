/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# The left unit law for the pullbacks on the small pro-étale sites

For `t : X ⟶ Y`, the composition isomorphism `(𝟙 X ≫ t)^* ≅ t^* ⋙ (𝟙 X)^*`
(`AlgebraicGeometry.ProEtale.upperStarComp`) followed by the identity isomorphism
`(𝟙 X)^* ≅ 𝟭` (`AlgebraicGeometry.ProEtale.upperStarId`) is the transport isomorphism
`(𝟙 X ≫ t)^* ≅ t^*` along `𝟙 X ≫ t = t`. This is obtained by conjugation from the
corresponding statement for the pushforwards, which is the left unit law of base change.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarComp_hom_app_comp_upperStarId_hom_app`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
private lemma pullbackCongr_hom_app_eq_inv_app {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (h' : g = f) (V : Y.ProEt) :
    (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h).hom.app V =
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h').inv.app V := by
  subst h
  simp [MorphismProperty.Over.pullbackCongr_refl]

set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
private lemma lowerStarComp_id_left_hom_app_aux (t : X ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarComp A (𝟙 X) t).hom.app M = (t)_*[A].map ((lowerStarId A X).hom.app M) ≫
      (lowerStarCongr A (Category.id_comp t).symm).hom.app M := by
  ext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStar_map_hom_app', lowerStarId_hom_app_hom_app]
  rw [MorphismProperty.Over.pullbackComp_id_left t (𝟙 X ≫ t) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
    pullbackCongr_hom_app_eq_inv_app _ (Category.id_comp t).symm]
  exact (congrArg M.obj.map op_comp).trans (M.obj.map_comp _ _)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The left unit law for the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_id_left_eq (t : X ⟶ Y) :
    lowerStarComp A (𝟙 X) t = Functor.isoWhiskerRight (lowerStarId A X) (t)_*[A] ≪≫
      (t)_*[A].leftUnitor ≪≫ (lowerStarCongr A (Category.id_comp t)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [lowerStarComp_id_left_hom_app_aux, Functor.comp_obj, lowerStarCongr_rfl,
    Iso.refl_symm, Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app,
    Functor.id_obj, Functor.whiskerRight_app, Functor.leftUnitor_hom_app, NatTrans.id_app,
    Category.id_comp]
  rfl

/-- The left unit law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_id_left_eq` by conjugation. -/
lemma upperStarComp_id_left_eq (t : X ⟶ Y) :
    upperStarComp A (𝟙 X) t = upperStarCongr A (Category.id_comp t) ≪≫
      (t)^*[A].rightUnitor.symm ≪≫ Functor.isoWhiskerLeft (t)^*[A] (upperStarId A X).symm := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A t).comp
    (upperStarLowerStarAdjunction A (𝟙 X))) (upperStarLowerStarAdjunction A (𝟙 X ≫ t))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A t) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A t).comp Adjunction.id) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor, lowerStarComp_id_left_eq]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp

/-- **Left unit law for the pullbacks**: the composition isomorphism
`(𝟙 X ≫ t)^* ≅ t^* ⋙ (𝟙 X)^*` followed by `(𝟙 X)^* ≅ 𝟭` is the transport isomorphism along
`𝟙 X ≫ t = t`. -/
@[reassoc]
lemma upperStarComp_hom_app_comp_upperStarId_hom_app (t : X ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A (𝟙 X) t).hom.app M ≫ (upperStarId A X).hom.app ((t)^*[A].obj M) =
      (upperStarCongr A (Category.id_comp t)).hom.app M := by
  rw [upperStarComp_id_left_eq]
  simp

end AlgebraicGeometry.ProEtale
