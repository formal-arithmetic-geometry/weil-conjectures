/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitComparisons

/-! # The affine chart limit over an upper tail

Source: Stacks Project, Tags 01ZR, 0095, 0097 and 01I6.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The fixed affine chart is the limit of its upper-tail stage charts.
Source: Stacks Project, Limits Tag 01ZR, first proof, affine case. -/
theorem exists_affine_chart_upper_tail_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
    let Z := W.X a
    ∃ (D : ({j : I // i ≤ j})ᵒᵖ ⥤ Scheme.{u}) (d : Cone D),
      Nonempty (IsLimit d) ∧ (∀ j, IsAffine (D.obj j)) ∧
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
  let D := upperTailChartDiagram R i (V.f a ≫ f)
  let d := upperTailChartCone R c i (V.f a ≫ f)
  have hd : Nonempty (IsLimit d) := upperTailChartCone_isLimit R c hc i (V.f a ≫ f)
  have haD : ∀ j, IsAffine (D.obj j) := by
    intro j
    let : IsAffine (V.X a) := ha
    change IsAffine (pullback (Spec.map (R.map (homOfLE j.unop.property))) (V.f a ≫ f))
    infer_instance
  obtain ⟨z, hz⟩ := affine_chart_upper_tail_limit_comparisons R c i f V a
  exact ⟨D, d, hd, haD, z, hz⟩

end AlgebraicGeometry
