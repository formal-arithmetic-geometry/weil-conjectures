/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimit
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Ring colimits of affine chart limits

Source: Stacks Project, Tags 01ZR, 0095, 0097 and 01I6.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A colimit presentation of the fixed affine chart ring, with geometric chart comparisons.
Source: Stacks Project, Limits Tag 01ZR, first proof, affine case; Tag 01I6. -/
theorem exists_affine_chart_ring_colimit_geometric
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
    let Z := W.X a
    ∃ F : {j : I // i ≤ j} ⥤ CommRingCat.{u},
      ∃ q : colimit F ≅ Γ(Z, ⊤),
      ∀ j : {j : I // i ≤ j},
        let U : (pullback f (Spec.map (R.map (homOfLE j.property)))).OpenCover.{u} :=
          V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE j.property))))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
        let Y := (U.pullback₁ p).X a
        ∃ (e : F.obj j ≅ Γ(U.X a, ⊤)) (h : Y ≅ Z),
          h.hom ≫ W.f a = (U.pullback₁ p).f a ∧
          colimit.ι F j ≫ q.hom ≫ (Scheme.Γ.mapIso h.op).hom =
            e.hom ≫ (U.pullbackHom p a).appTop := by
  classical
  dsimp
  obtain ⟨D, d, ⟨hd⟩, haD, z, hcompare⟩ :=
    exists_affine_chart_upper_tail_limit R c hc i f V a ha
  let : ∀ j, IsAffine (D.obj j) := haD
  let : ∀ j, IsAffine (D.rightOp.obj j).unop := fun j ↦ haD (op j)
  let F := D.rightOp ⋙ Scheme.Γ
  let dΓ := Scheme.Γ.mapCocone (coconeRightOpOfCone d)
  have hdΓ : IsColimit dΓ := isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone D hd)
  let q₀ : colimit F ≅ Γ(d.pt, ⊤) :=
    (colimit.isColimit F).coconePointUniqueUpToIso hdΓ
  let q := q₀ ≪≫ (Scheme.Γ.mapIso z.op).symm
  refine ⟨F, q, ?_⟩
  intro j
  obtain ⟨e, h, hg, hπ⟩ := hcompare j
  refine ⟨(Scheme.Γ.mapIso e.op).symm, h, hg, ?_⟩
  have hι : colimit.ι F j ≫ q₀.hom = (d.π.app (op j)).appTop :=
    (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hdΓ j
  change colimit.ι F j ≫ (q₀.hom ≫ z.inv.appTop) ≫ h.hom.appTop =
    e.inv.appTop ≫ _
  simp only [← Category.assoc]
  rw [hι]
  have hp := congrArg Scheme.Hom.appTop hπ
  simp only [Scheme.Hom.comp_appTop] at hp
  rw [← hp]
  have he : e.inv.appTop ≫ e.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]
    rfl
  simp only [← Category.assoc, he, Category.id_comp]

end AlgebraicGeometry
