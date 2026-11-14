/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleUnionHomotopyChainData
import WeilConjectures.CategoryTheory.DerivedCategory.HomotopySquareRectification

/-! # Chain representatives of the single-module union comparison

Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private lemma transport_comparison
    {E : Type*} [Category E] {X Y Z X' Z' : E}
    (e : X ≅ Y) (e₂ : Y ≅ Z) (e₂' : X' ≅ Z')
    {b : X ⟶ X'} {β : Y ⟶ X'} {f : Z ⟶ Z'}
    (hb : b = e.hom ≫ β) (hβ : β ≫ e₂'.hom = e₂.hom ≫ f) :
    b ≫ e₂'.hom = (e ≪≫ e₂).hom ≫ f := by
  calc
    b ≫ e₂'.hom = (e.hom ≫ β) ≫ e₂'.hom := congrArg (· ≫ e₂'.hom) hb
    _ = e.hom ≫ (β ≫ e₂'.hom) := Category.assoc _ _ _
    _ = e.hom ≫ (e₂.hom ≫ f) := congrArg (e.hom ≫ ·) hβ
    _ = (e ≪≫ e₂).hom ≫ f := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
-- Transporting the standard derived-category instances needs extra elaboration heartbeats.
/-- A strict first-map square whose cones represent the overlap comparisons.
Unlike a short exact presentation, this asserts no monomorphism, epimorphism,
short complex or exactness of complexes on A.

Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY, 0DJ9, 013N--013O. -/
theorem standardSingle_union_ses_chain_data
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (hc : t ≫ β = α ≫ t')
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  obtain ⟨C, D, C', D', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hcone⟩ :=
    standardSingle_union_homotopy_chain_data p g U V N
  obtain ⟨T, i, b, hc, d₂, d₃, hb, hq⟩ :=
    CochainComplex.homotopy_square_cone_rectification t t' α β H
  refine ⟨C, T, C', D', i, t', α, b, hc, e₁, d₂ ≪≫ e₂, d₃ ≪≫ e₃,
    e₁', e₂', e₃', hα, ?_, ?_⟩
  · exact transport_comparison d₂ e₂ e₂' hb hβ
  · exact transport_comparison d₃ e₃ e₃' hq hcone

end AlgebraicGeometry
