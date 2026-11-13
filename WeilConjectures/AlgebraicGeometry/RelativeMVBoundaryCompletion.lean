/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.RelativeMVSESPresentation

/-! # Compatible relative Mayer--Vietoris boundaries

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Complete the fixed relative restriction sequences by compatible boundaries.
This asserts distinguishedness and only the connecting square; it does not assert
commutativity of either restriction square. -/
theorem relativeMV_boundary_completion
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
    ∃ (δ : (a (U ⊓ V)).left ⟶ aX.left⟦(1 : ℤ)⟧)
      (δ' : (a (U ⊓ V)).right ⟶ aX.right⟦(1 : ℤ)⟧),
      Triangle.mk (relativeMVSourceFirst f g U V K)
        (relativeMVSourceSecond f g U V K) δ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk (relativeMVTargetFirst g' f' U V K')
        (relativeMVTargetSecond g' f' U V K') δ' ∈ distTriang (schemeDerivedCategory S') ∧
      δ ≫ aX.hom⟦(1 : ℤ)⟧' = (a (U ⊓ V)).hom ≫ δ' := by
  classical
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', hf, hg, hf', hg', h₁, h₃⟩ :=
    relativeMV_ses_presentation f f' g g' hpull K K' φ
      U V hcover
  let δ := e₃.inv ≫ DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧'
  let δ' := e₃'.inv ≫ DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧'
  refine ⟨δ, δ', ?_, ?_, ?_⟩
  · apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP)
    refine (Triangle.isoMk _ _ e₁ e₂ e₃ hf hg ?_).symm
    change DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ
    simp only [δ, Iso.hom_inv_id_assoc]
  · apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP')
    refine (Triangle.isoMk _ _ e₁' e₂' e₃' hf' hg' ?_).symm
    change DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧' = e₃'.hom ≫ δ'
    simp only [δ', Iso.hom_inv_id_assoc]
  · have hn := DerivedCategory.triangleOfSESδ_naturality hP hP' m
    have hshift := congrArg (fun t ↦ t⟦(1 : ℤ)⟧') h₁
    simp only [Functor.map_comp] at hshift
    have h₃inv : e₃.inv ≫ DerivedCategory.Q.map m.τ₃ =
        (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom ≫ e₃'.inv := by
      apply (cancel_mono e₃'.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h₃]
      simp only [Iso.inv_hom_id_assoc]
    dsimp only [δ, δ']
    simp only [Category.assoc]
    rw [← hshift, ← Category.assoc (DerivedCategory.triangleOfSESδ hP), hn]
    simp only [← Category.assoc]
    rw [h₃inv]

end AlgebraicGeometry
