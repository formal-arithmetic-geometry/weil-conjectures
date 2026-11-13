/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.RelativeMVPinnedTriangleComparison
import WeilConjectures.CategoryTheory.DerivedCategory.EndpointConePresentation

/-! # A mapping-cone model of the relative Mayer--Vietoris diagram

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry

/-- Construct a strict square of first restriction maps whose functorial cones
compute the two relative overlap terms. This is the enhanced Mayer--Vietoris
construction; no short exact replacement on the base is required here. -/
theorem relativeMV_cone_presentation
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
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ aX.left)
      (e₂ : DerivedCategory.Q.obj B ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ aX.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ (a (U ⊓ V)).right),
      DerivedCategory.Q.map t ≫ e₂.hom = e₁.hom ≫ relativeMVSourceFirst f g U V K ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr t) ≫ e₃.hom =
        e₂.hom ≫ relativeMVSourceSecond f g U V K ∧
      DerivedCategory.Q.map t' ≫ e₂'.hom =
        e₁'.hom ≫ relativeMVTargetFirst g' f' U V K' ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr t') ≫ e₃'.hom =
        e₂'.hom ≫ relativeMVTargetSecond g' f' U V K' ∧
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ aX.hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (a (U ⊓ V)).hom  := by
  dsimp only
  obtain ⟨δ, δ', hT, hT', m, h₁, _, h₃⟩ :=
    relativeMV_pinned_triangle_comparison f f' g g' hpull K K' φ
      U V hcover
  have hc := m.comm₃
  rw [h₁, h₃] at hc
  exact derived_endpoint_cone_presentation
    (Pretriangulated.Triangle.mk (relativeMVSourceFirst f g U V K)
      (relativeMVSourceSecond f g U V K) δ)
    (Pretriangulated.Triangle.mk (relativeMVTargetFirst g' f' U V K')
      (relativeMVTargetSecond g' f' U V K') δ')
    hT hT' (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom
    (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom hc

end AlgebraicGeometry
