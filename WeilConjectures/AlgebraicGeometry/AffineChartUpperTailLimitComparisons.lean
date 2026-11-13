/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitData

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- Pullback-pasting comparisons for the explicitly constructed upper-tail chart cone.
Source: Stacks Project, Limits Tags 01ZR, 0095 and 0097. -/
theorem affine_chart_upper_tail_limit_comparisons
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec))
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (V : Xi.OpenCover.{u}) (a : V.I₀) :
    let D := upperTailChartDiagram R i (V.f a ≫ f)
    let d := upperTailChartCone R c i (V.f a ≫ f)
    let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
    let Z := W.X a
    ∃ z : d.pt ≅ Z, ∀ j : {j : I // i ≤ j},
      let U : (pullback f (Spec.map (R.map (homOfLE j.property)))).OpenCover.{u} :=
        V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE j.property))))
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
      let Y := (U.pullback₁ p).X a
      ∃ (e : D.obj (op j) ≅ U.X a) (h : Y ≅ Z),
        h.hom ≫ W.f a = (U.pullback₁ p).f a ∧
        h.hom ≫ z.inv ≫ d.π.app (op j) ≫ e.hom = U.pullbackHom p a := by
  let q := c.π.app (op i)
  let v := V.f a
  let z : pullback q (v ≫ f) ≅ pullback (pullback.fst f q) v :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso f q v).symm ≪≫
      pullbackSymmetry _ _
  refine ⟨z, ?_⟩
  intro j
  let r := Spec.map (R.map (homOfLE j.property))
  let p := baseChangeMap f
    (T := Over.mk r) (T' := Over.mk q)
    (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
  let e : pullback r (v ≫ f) ≅ pullback (pullback.fst f r) v :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso f r v).symm ≪≫
      pullbackSymmetry _ _
  have hp : p ≫ pullback.fst f r = pullback.fst f q := by
    simp [p, baseChangeMap]
  let h : pullback p (pullback.fst (pullback.fst f r) v) ≅
      pullback (pullback.fst f q) v :=
    pullbackRightPullbackFstIso (pullback.fst f r) v p ≪≫ pullback.congrHom hp rfl
  refine ⟨e, h, ?_, ?_⟩
  · change h.hom ≫ pullback.fst _ _ = pullback.fst _ _
    simp [h]
  · change h.hom ≫ z.inv ≫
      ((Over.pullback (v ≫ f)).map
        (Over.homMk (U := Over.mk q) (V := Over.mk r)
          (c.π.app (op j.val)) (c.w (homOfLE j.property).op))).left ≫
        e.hom = pullback.snd _ _
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Functor.const_obj_obj, Over.mk_left, Over.mk_hom, baseChangeMap,
          Iso.trans_hom, pullback.congrHom_hom, Functor.comp_obj, Functor.op_obj,
          Scheme.Spec_obj, Iso.trans_inv, Iso.symm_inv, Category.assoc, Over.pullback,
          Over.homMk_left, Iso.symm_hom, pullbackSymmetry_hom_comp_fst,
          pullbackRightPullbackFstIso_inv_snd_fst, pullbackSymmetry_hom_comp_fst_assoc,
          limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
          pullbackSymmetry_inv_comp_snd_assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
          pullbackSymmetry_inv_comp_fst_assoc, Category.comp_id,
          pullbackRightPullbackFstIso_hom_snd_assoc, p, h, z, e]
        rw [← pullback.condition (f := pullback.fst f r) (g := v)]
      · simp only [Functor.const_obj_obj, Over.mk_left, Over.mk_hom, baseChangeMap,
          Iso.trans_hom, pullback.congrHom_hom, Functor.comp_obj, Functor.op_obj,
          Scheme.Spec_obj, Iso.trans_inv, Iso.symm_inv, Category.assoc, Over.pullback,
          Over.homMk_left, Iso.symm_hom, pullbackSymmetry_hom_comp_fst,
          pullbackRightPullbackFstIso_inv_snd_snd, pullbackSymmetry_hom_comp_snd,
          limit.lift_π, PullbackCone.mk_π_app, pullbackSymmetry_inv_comp_fst_assoc,
          pullbackRightPullbackFstIso_hom_snd_assoc, pullbackSymmetry_inv_comp_snd_assoc,
          limit.lift_π_assoc, cospan_left, Category.comp_id,
          pullbackRightPullbackFstIso_hom_fst_assoc, p, h, z, e]
        change pullback.fst p (pullback.fst (pullback.fst f r) v) ≫
          pullback.snd f q ≫ c.π.app (op j.val) =
          pullback.snd p (pullback.fst (pullback.fst f r) v) ≫
            pullback.fst (pullback.fst f r) v ≫ pullback.snd f r
        rw [← pullback.condition_assoc (f := p) (g := pullback.fst (pullback.fst f r) v)]
        simp [p, baseChangeMap]
    · simp [h, z, e, Over.pullback, Category.assoc]

end AlgebraicGeometry
