/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.RelativeMVConePresentation
import WeilConjectures.CategoryTheory.DerivedCategory.ConeDiagramSESPresentation

/-! # Chain-level relative Mayer--Vietoris presentation

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry

/-- Present the relative Mayer--Vietoris comparison by a morphism of short exact
complexes. No connecting morphisms or distinguished triangles are asserted. -/
theorem relativeMV_ses_presentation
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVLocalArrow f f' g g' hpull K K' φ
    let aX := relativeMVGlobalArrow f f' g g' hpull K K' φ
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ aX.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ aX.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (a (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map P.f ≫ e₂.hom = e₁.hom ≫ relativeMVSourceFirst f g U V K ∧
      DerivedCategory.Q.map P.g ≫ e₃.hom = e₂.hom ≫ relativeMVSourceSecond f g U V K ∧
      DerivedCategory.Q.map P'.f ≫ e₂'.hom =
        e₁'.hom ≫ relativeMVTargetFirst g' f' U V K' ∧
      DerivedCategory.Q.map P'.g ≫ e₃'.hom =
        e₂'.hom ≫ relativeMVTargetSecond g' f' U V K' ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ aX.hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ (a (U ⊓ V)).hom := by
  obtain ⟨A, B, A', B', t, t', α, β, hc, e₁, e₂, e₃, e₁', e₂', e₃',
    hf, hg, hf', hg', h₁, h₃⟩ :=
    relativeMV_cone_presentation f f' g g' hpull K K' φ
      U V hcover
  obtain ⟨P, P', m, d₁, d₂, d₃, d₁', d₂', d₃', hP, hP',
    kf, kg, kf', kg', k₁, k₃⟩ :=
    cone_diagram_ses_presentation A B A' B' t t' α β hc
  refine ⟨P, P', m, d₁ ≪≫ e₁, d₂ ≪≫ e₂, d₃ ≪≫ e₃,
    d₁' ≪≫ e₁', d₂' ≪≫ e₂', d₃' ≪≫ e₃', hP, hP', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc, hf] using
      congrArg (fun k ↦ k ≫ e₂.hom) kf
  · simpa only [Iso.trans_hom, Category.assoc, hg] using
      congrArg (fun k ↦ k ≫ e₃.hom) kg
  · simpa only [Iso.trans_hom, Category.assoc, hf'] using
      congrArg (fun k ↦ k ≫ e₂'.hom) kf'
  · simpa only [Iso.trans_hom, Category.assoc, hg'] using
      congrArg (fun k ↦ k ≫ e₃'.hom) kg'
  · simpa only [Iso.trans_hom, Category.assoc, h₁] using
      congrArg (fun k ↦ k ≫ e₁'.hom) k₁
  · simpa only [Iso.trans_hom, Category.assoc, h₃] using
      congrArg (fun k ↦ k ≫ e₃'.hom) k₃

end AlgebraicGeometry
