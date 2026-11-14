/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVCoverHomotopyData
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleOpenRelativeArrow

/-! # Homotopy representatives of the resolved cover comparison -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem transport_comparison
    {T : Type*} [Category T] {X Y : T} {a b : Arrow T}
    (q : X ⟶ Y) (e : X ≅ a.left) (e' : Y ≅ a.right) (i : a ≅ b)
    (h : q ≫ e'.hom = e.hom ≫ a.hom) :
    q ≫ (e' ≪≫ Arrow.rightFunc.mapIso i).hom =
      (e ≪≫ Arrow.leftFunc.mapIso i).hom ≫ b.hom := by
  change q ≫ (e'.hom ≫ i.hom.right) = (e.hom ≫ i.hom.left) ≫ b.hom
  rw [← Category.assoc, h, Category.assoc, ← Arrow.w, ← Category.assoc]

private theorem transport_biprod_comparison
    {T : Type*} [Category T] [HasZeroMorphisms T] [HasBinaryBiproducts T]
    {X Y : T} {a₁ a₂ b₁ b₂ : Arrow T}
    (q : X ⟶ Y) (e : X ≅ a₁.left ⊞ a₂.left)
    (e' : Y ≅ a₁.right ⊞ a₂.right) (i₁ : a₁ ≅ b₁) (i₂ : a₂ ≅ b₂)
    (h : q ≫ e'.hom = e.hom ≫ biprod.map a₁.hom a₂.hom) :
    q ≫ (e' ≪≫ biprod.mapIso
        (Arrow.rightFunc.mapIso i₁) (Arrow.rightFunc.mapIso i₂)).hom =
      (e ≪≫ biprod.mapIso
        (Arrow.leftFunc.mapIso i₁) (Arrow.leftFunc.mapIso i₂)).hom ≫
          biprod.map b₁.hom b₂.hom := by
  simp only [Iso.trans_hom, biprod.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  congr 1
  change biprod.map a₁.hom a₂.hom ≫ biprod.map i₁.hom.right i₂.hom.right =
    biprod.map i₁.hom.left i₂.hom.left ≫ biprod.map b₁.hom b₂.hom
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc] using
      congrArg (fun k ↦ biprod.fst ≫ k) i₁.hom.w.symm
  · simpa only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc] using
      congrArg (fun k ↦ biprod.snd ≫ k) i₂.hom.w.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Transporting the relative comparison requires additional elaboration heartbeats.
/-- The resolved cover comparison before cylinder rectification.
Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY and 0DJ9. -/
theorem standardSingle_union_homotopy_chain_data
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
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let W := U ⊔ V
  let f := W.ι ≫ p
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N)
  let φ := Scheme.picardTermwiseSingleMap (pullback.fst f g) N
  have hcover : (W.ι ⁻¹ᵁ U) ⊔ (W.ι ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup]
    exact W.ι_preimage_self
  obtain ⟨C, D, C', D', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ :=
    relativeMV_cover_homotopy_data f (pullback.snd f g) g (pullback.fst f g)
      (IsPullback.of_hasPullback f g) K K' φ (W.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ V) hcover
  obtain ⟨iU⟩ := standardSingle_open_relative_arrow p g W U le_sup_left N
  obtain ⟨iV⟩ := standardSingle_open_relative_arrow p g W V le_sup_right N
  obtain ⟨iUV⟩ := standardSingle_open_relative_arrow p g W (U ⊓ V)
    (inf_le_left.trans le_sup_left) N
  let lU := Arrow.leftFunc.mapIso iU
  let rU := Arrow.rightFunc.mapIso iU
  let lV := Arrow.leftFunc.mapIso iV
  let rV := Arrow.rightFunc.mapIso iV
  let lUV := Arrow.leftFunc.mapIso iUV
  let rUV := Arrow.rightFunc.mapIso iUV
  refine ⟨C, D, C', D', t, t', α, β, H, e₁,
    e₂ ≪≫ biprod.mapIso lU lV, e₃ ≪≫ lUV, e₁',
    e₂' ≪≫ biprod.mapIso rU rV, e₃' ≪≫ rUV, ?_, ?_, ?_⟩
  · exact hα
  · exact transport_biprod_comparison _ e₂ e₂' iU iV hβ
  · exact transport_comparison _ e₃ e₃' iUV hγ

end AlgebraicGeometry
