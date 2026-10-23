/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Reflection
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# The convolution of the Fourier kernels

For lisse Weil sheaves `𝒦`, `𝒦'` on `𝔸¹ ×_{k₀} 𝔸¹`, the *convolution*
`𝒦' ∗ 𝒦 = Rr₁₃!(r₁₂^* 𝒦 ⊗ r₂₃^* 𝒦')` is a Weil complex on `𝔸¹ ×_{k₀} 𝔸¹`
(`AlgebraicGeometry.WeilComplex.kernelConvolution`), the triple product `𝔸³` having points
`(x, ξ, y)`. For the Fourier kernels `𝒦_ψ = μ^* ℒ_ψ` and a nontrivial character `ψ`
(blueprint `lem-fd-convolution-kernel`, `sk-prop-convolution-kernel`):

* `𝒦_{ψ⁻¹} ∗ 𝒦_ψ ≅ RΔ!(ℚ̄_ℓ(-1)[-2])`, the constant sheaf on the diagonal
  (`AlgebraicGeometry.nonempty_iso_kernelConvolution_fourierKernel_inv`);
* `𝒦_ψ ∗ 𝒦_ψ ≅ R(1 × ι')Δ!(ℚ̄_ℓ(-1)[-2])`, the constant sheaf on the antidiagonal
  (`AlgebraicGeometry.nonempty_iso_kernelConvolution_fourierKernel`).

The integrand is `ℒ_ψ((x ∓ y) ξ)` and the delta kernel computation
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul`)
for the function `x ∓ y` on `𝔸²` concentrates it on the zero locus.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The pullback of the constant Weil complex `ℚ̄_ℓ` is the constant Weil complex. -/
noncomputable def WeilComplex.upperStarAdicConstantIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (WeilComplex.upperStar φ).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X) :=
  (WeilSheaf.toComplexCompUpperStarIso φ).app _ ≪≫
    WeilSheaf.toComplex.mapIso (WeilSheaf.upperStarAdicConstantIso φ)

/-- The *convolution* `𝒦' ∗ 𝒦 = Rr₁₃!(r₁₂^* 𝒦 ⊗ r₂₃^* 𝒦')` of two lisse Weil sheaves on
`𝔸¹ ×_{k₀} 𝔸¹`, a Weil complex on `𝔸¹ ×_{k₀} 𝔸¹` (blueprint `lem-fd-kernel-composition`); the
tensor product `r₁₂^* 𝒦 ⊗ r₂₃^* 𝒦'` is that of the constant complex `ℚ̄_ℓ` on the triple product
with the two lisse sheaves. -/
noncomputable def WeilComplex.kernelConvolution (𝒦 𝒦' : WeilSheaf k₀ l (affinePlane k₀))
    (h𝒦 : 𝒦.IsLisse) (h𝒦' : 𝒦'.IsLisse) : WeilComplex k₀ l (affinePlane k₀) :=
  (WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀)).obj
    ((WeilComplex.tensorLisse ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj 𝒦')
      (h𝒦'.upperStar _)).obj
      ((WeilComplex.tensorLisse ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj 𝒦)
        (h𝒦.upperStar _)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineTripleProduct k₀)))))

/-- The Fourier kernels for `ψ` and `ψ⁻¹` pulled back to the triple product `𝔸³` with points
`(x, ξ, y)` multiply to `ℒ_ψ((x - y) ξ)`: tensoring with `r₁₂^* μ^* ℒ_ψ` and then with
`r₂₃^* μ^* ℒ_{ψ⁻¹}` is tensoring with `ℒ_ψ((x - y) ξ)` (blueprint `lem-fd-as-lisse`). -/
theorem WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_sub
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj (fourierKernel (l := l) ψ))
        ((isLisse_fourierKernel ψ).upperStar _) ⋙
      WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj (fourierKernel ψ⁻¹))
        ((isLisse_fourierKernel ψ⁻¹).upperStar _) ≅
      WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop
                (AffineSpace.coord _ PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _)) := by
  have h₁₂₃ : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
      affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
    pullback.condition.symm
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
  -- the kernels as Artin–Schreier sheaves on `𝔸³`
  obtain ⟨eF⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ
  obtain ⟨eF₁⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ⁻¹
  have eF' : fourierKernel (l := l) ψ ≅ artinSchreierOf ψ m := eF
  have eF₁' : fourierKernel (l := l) ψ⁻¹ ≅ artinSchreierOf ψ⁻¹ m := eF₁
  obtain ⟨eG₁⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₁₂ k₀) ψ m
  obtain ⟨eG₂⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₂₃ k₀) ψ⁻¹ m
  obtain ⟨eInv⟩ := nonempty_iso_artinSchreierOf_inv ψ ((affineTripleProduct.proj₂₃ k₀).appTop m)
  obtain ⟨eT₁⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).mapIso eF' ≪≫ eG₁)
    ((isLisse_fourierKernel ψ).upperStar _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).mapIso eF₁' ≪≫ eG₂ ≪≫ eInv)
    ((isLisse_fourierKernel ψ⁻¹).upperStar _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₁₂⟩ := WeilComplex.nonempty_iso_tensorLisse_comp
    (artinSchreierOf ψ (-(affineTripleProduct.proj₂₃ k₀).appTop m))
    (artinSchreierOf ψ ((affineTripleProduct.proj₁₂ k₀).appTop m))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eMul⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ
    (-(affineTripleProduct.proj₂₃ k₀).appTop m) ((affineTripleProduct.proj₁₂ k₀).appTop m)
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (eMul ≪≫ eqToIso (congrArg (artinSchreierOf ψ) hring))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ _).dual
      (isLisse_artinSchreierOf ψ _))
    (isLisse_artinSchreierOf ψ _)
  exact ⟨Functor.isoWhiskerRight eT₁ _ ≪≫ Functor.isoWhiskerLeft _ eT₂ ≪≫ eT₁₂ ≪≫ eT⟩

/-- **The convolution of the Fourier kernels is the delta kernel** (blueprint
`lem-fd-convolution-kernel`, `sk-prop-convolution-kernel`, first formula): for a nontrivial
additive character `ψ`,

`𝒦_{ψ⁻¹} ∗ 𝒦_ψ ≅ RΔ!(ℚ̄_ℓ(-1)[-2])`,

the constant sheaf with Tate twist `(-1)` and shift `[-2]` extended by zero along the diagonal
`Δ : 𝔸¹ ⟶ 𝔸¹ ×_{k₀} 𝔸¹`. The integrand on `𝔸³` is `ℒ_ψ((x - y) ξ)`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_sub`), and
the compact-support direct image along `r₁₃` concentrates it on the zero locus of `x - y`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul`).
-/
theorem nonempty_iso_kernelConvolution_fourierKernel_inv (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) :
    Nonempty (WeilComplex.kernelConvolution (fourierKernel ψ) (fourierKernel ψ⁻¹)
        (isLisse_fourierKernel ψ) (isLisse_fourierKernel ψ⁻¹) ≅
      (WeilComplex.derivedLowerShriek k₀ l (affineLine.diagonal k₀)).obj
        ((shiftFunctor _ (-2 : ℤ)).obj ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀)))))) := by
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_sub (l := l) ψ
  obtain ⟨e₄⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (l := l) ψ hψ (affinePlane.sub k₀)
    (affineTripleProduct.proj₁₃ k₀) (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀)
    affineTripleProduct.isPullback_proj₁₃ (affineLine.diagonal k₀)
    (AffineSpace.isPullback_diagonal_sub _ _)
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affinePlane k₀))
  exact ⟨(WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀)).mapIso
      (eT.app _ ≪≫ (WeilComplex.tensorLisse _ (isLisse_artinSchreierOf ψ _)).mapIso
        (WeilComplex.upperStarAdicConstantIso (affineTripleProduct.proj₁₃ k₀)).symm) ≪≫
    e₄.app U ≪≫
    (WeilComplex.derivedLowerShriek k₀ l (affineLine.diagonal k₀)).mapIso
      ((shiftFunctor _ (-2 : ℤ)).mapIso ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).mapIso
        (WeilComplex.upperStarAdicConstantIso (affineLine.diagonal k₀))))⟩

/-- **The convolution of the Fourier kernel with itself** (blueprint
`lem-fd-convolution-kernel`, `sk-prop-convolution-kernel`, second formula): for a nontrivial
additive character `ψ`,

`𝒦_ψ ∗ 𝒦_ψ ≅ R((1 × ι') ∘ Δ)!(ℚ̄_ℓ(-1)[-2])`,

the constant sheaf with Tate twist `(-1)` and shift `[-2]` extended by zero along the
antidiagonal `x ↦ (x, -x)`, the image of the diagonal under `1 × ι'`. The integrand on `𝔸³` is
`ℒ_ψ((x + y) ξ)`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_add`), and
the compact-support direct image along `r₁₃` concentrates it on the zero locus of `x + y`. -/
theorem nonempty_iso_kernelConvolution_fourierKernel (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) :
    Nonempty (WeilComplex.kernelConvolution (fourierKernel ψ) (fourierKernel ψ)
        (isLisse_fourierKernel ψ) (isLisse_fourierKernel ψ) ≅
      (WeilComplex.derivedLowerShriek k₀ l (affineLine.antidiagonal k₀)).obj
        ((shiftFunctor _ (-2 : ℤ)).obj ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀)))))) := by
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_add (l := l) ψ
  obtain ⟨e₄⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (l := l) ψ hψ (affinePlane.add k₀)
    (affineTripleProduct.proj₁₃ k₀) (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀)
    affineTripleProduct.isPullback_proj₁₃ (affineLine.antidiagonal k₀)
    (AffineSpace.isPullback_diagonal_prodNeg_add _ _)
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affinePlane k₀))
  exact ⟨(WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀)).mapIso
      (eT.app _ ≪≫ (WeilComplex.tensorLisse _ (isLisse_artinSchreierOf ψ _)).mapIso
        (WeilComplex.upperStarAdicConstantIso (affineTripleProduct.proj₁₃ k₀)).symm) ≪≫
    e₄.app U ≪≫
    (WeilComplex.derivedLowerShriek k₀ l (affineLine.antidiagonal k₀)).mapIso
      ((shiftFunctor _ (-2 : ℤ)).mapIso ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).mapIso
        (WeilComplex.upperStarAdicConstantIso (affineLine.antidiagonal k₀))))⟩

end AlgebraicGeometry
