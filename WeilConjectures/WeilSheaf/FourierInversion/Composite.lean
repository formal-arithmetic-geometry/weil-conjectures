/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing
public import WeilConjectures.WeilSheaf.FourierTraceAux

/-!
# Fourier inversion: the composite of two Fourier transforms

`FT_{ψ⁻¹} ∘ FT_ψ` computed on the triple product `𝔸³` (blueprint `lem-fd-kernel-composition`).
-/

@[expose] public section

set_option profiler true

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Pullbacks of Weil sheaves along equal morphisms agree. -/
theorem WeilSheaf.upperStar_eq_of_eq {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {f g : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] (h : f = g) :
    (WeilSheaf.upperStar f : WeilSheaf k₀ l Y ⥤ _) = WeilSheaf.upperStar g := by
  subst h
  rfl

omit [Finite k₀] in
/-- The multiplication `μ : 𝔸² ⟶ 𝔸¹` is the morphism defined by the function `x y`. -/
theorem affinePlane.mul_eq_homOfSection :
    affinePlane.mul k₀ = affineLine.homOfSection k₀
      ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)) := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [affinePlane.mul, affineLine.homOfSection, AffineSpace.homOfVector_over]
  · rw [affinePlane.mul, affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord]

/-- The Fourier kernel `μ^* ℒ_ψ` is the Artin–Schreier sheaf `ℒ_ψ(x y)` of the function `x y`. -/
theorem fourierKernel_eq_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierKernel ψ = artinSchreierOf ψ
      ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)) := by
  rw [fourierKernel, artinSchreierOf]
  exact Functor.congr_obj (WeilSheaf.upperStar_eq_of_eq affinePlane.mul_eq_homOfSection) _


/-- **`FT_{ψ⁻¹} ∘ FT_ψ` on the triple product** (blueprint `lem-fd-kernel-composition`,
`sk-lem-kernel-composition`, without forming the convolution kernel). On `𝔸³` with points
`(x, ξ, y)`,

`FT_{ψ⁻¹} FT_ψ (K) ≅ Rr₃₀!(ℒ_ψ((x - y) ξ) ⊗ r₁^* K)[1][1]`

naturally in `K`, with `r₁ = r₁₃ ≫ pr₁` and `r₃ = r₁₃ ≫ pr₂`. It follows from compact-support
base change along `pr₁ : (ξ, y) ↦ ξ`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`), the projection
formula for `r₂₃` and the composition `R(r₂₃ ≫ pr₂)₀! ≅ Rpr₂₀! Rr₂₃₀!`, together with
`ℒ_ψ(x ξ) ⊗ ℒ_{ψ⁻¹}(ξ y) ≅ ℒ_ψ((x - y) ξ)` (blueprint `lem-fd-as-lisse`). -/
theorem nonempty_iso_fourierTransform_comp_fourierTransform_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop
                (AffineSpace.coord _ PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) := by
  have : QuasiCompact (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have : QuasiCompact (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
    exact inferInstanceAs (QuasiCompact (affinePlane.fst k₀ ≫ _))
  have : QuasiSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have : QuasiSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
    exact inferInstanceAs (QuasiSeparated (affinePlane.fst k₀ ≫ _))
  have h₁₂₃ : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
      affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
    pullback.condition.symm
  have : (affineTripleProduct.proj₁₂ k₀).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (affineTripleProduct.proj₂₃ k₀).IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨by
      rw [← comp_over (affinePlane.fst k₀) (Spec (CommRingCat.of k₀)), reassoc_of% h₁₂₃,
        comp_over (affinePlane.snd k₀)]
      rfl⟩
  have : IsSeparated (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  -- the functions `x ξ` on `𝔸²` and `(x - y) ξ` on `𝔸³`
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  have hring : -(affineTripleProduct.proj₂₃ k₀).appTop m +
      (affineTripleProduct.proj₁₂ k₀).appTop m =
      (affineTripleProduct.proj₁₃ k₀).appTop
          ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop X₁) *
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
    have e₁ : (affineTripleProduct.proj₁₃ k₀).appTop
        ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop X₁) =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ -
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
      rw [AffineSpace.sub_appTop_coord, map_sub]
      exact congrArg₂ (· - ·)
        (congrArg (fun f ↦ Scheme.Hom.appTop f X₁) (pullback.tripleProj₁₃_fst _ _ _))
        (congrArg (fun f ↦ Scheme.Hom.appTop f X₁) (pullback.tripleProj₁₃_snd _ _ _))
    have e₂ : (affineTripleProduct.proj₂₃ k₀).appTop m =
        (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀).appTop X₁ *
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ :=
      map_mul _ _ _
    have e₃ : (affineTripleProduct.proj₁₂ k₀).appTop m =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ *
          (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ :=
      map_mul _ _ _
    rw [e₁, e₂, e₃, h₁₂₃]
    ring
  sorry

end AlgebraicGeometry
