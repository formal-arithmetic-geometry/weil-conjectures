/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!

# Invertibility of the Fourier–Deligne transform

Kernel transforms compose: the composite of the kernel transforms of `𝒦` and `𝒦'` is the
kernel transform of the convolution `𝒦' ∗ 𝒦`, with the shifts added
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`). Applied to the Fourier kernels
this reduces the inversion theorem to a single computation, that the convolution of
`𝒦_{ψ⁻¹}` with `𝒦_ψ` is the delta kernel `Δ_* Λ(-r)[-2r]`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`: the convolution of the two
  Fourier kernels is the delta kernel.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution_self`: the convolution of the
  Fourier kernel with itself is the delta kernel of the anti-diagonal.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_self`: the inversion
  theorem, proved from the statements above.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The statements only assert that an isomorphism *exists*. Showing that `FT_ψ` is an
equivalence with inverse `FT_{ψ⁻¹}(r)` will need specific, coherent isomorphisms, which
`Classical.choice` cannot provide.

The blueprint computes the convolution of the kernels stalk by stalk. Here it is computed
globally, which also produces the map to the delta kernel that a stalk computation needs. On the
triple product `(x, ξ, y)` the integrand `r₁₂^* 𝒦_ψ ⊗ᴸ r₂₃^* 𝒦_{ψ⁻¹}` is the Artin–Schreier
sheaf of `⟨ξ, x - y⟩`, the pullback of `𝒦_ψ` along the shear `(x, ξ, y) ↦ (ξ, x - y)`, which
makes `r₁₃` a base change of the second projection `p₂` along the subtraction. Compact-support
base change turns the convolution into `sub^* Rp₂,! 𝒦_ψ`. Up to the shift `[r]`, `Rp₂,! 𝒦_ψ`
is the transform of the constant sheaf, `δ₀(-r)[-2r]`
(`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`, whose fibrewise content
is the blueprint's: `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]` and `H_c^*(𝔸¹, ℒ_ψ) = 0`). Finally
`sub^* δ₀ ≅ Δ_* Λ`, the diagonal being the fibre of the subtraction over the origin. The
same-character case replaces the subtraction by the addition and the diagonal by the
anti-diagonal.

Rewriting with `AlgebraicGeometry.Etale.kernelConvolution_eq`, and stating the intermediate
steps for arbitrary cartesian squares, keeps the kernel from comparing large derived-category
terms that differ only in how a scheme or a definition is unfolded: those comparisons time out.

TODO: upgrade these back to `Iso` constructions once they can be built.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

section ConvolutionKernel

variable (n : Type u) [Fintype n] (S : Scheme.{u})

/-- The compactly supported direct image of the Fourier kernel along the second projection is
the skyscraper at the origin, Tate twisted by `(-r)` and shifted by `-2r`, `r = #n`:

`Rp₂,! 𝒦_ψ ≅ δ₀(-r)[-2r]`.

At a geometric point `c` this is `RΓ_c(𝔸^r, ℒ_{ψ(⟨ξ, c⟩)})`, which vanishes for `c ≠ 0` and is
`Λ(-r)[-2r]` for `c = 0`. It is the transform of the constant sheaf
(`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`) with the shift `[r]` of the
transform removed, `p₁^* Λ ⊗ᴸ 𝒦_ψ` being `𝒦_ψ`.
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_rightDerivedLowerShriek_fourierKernel [Finite Λ]
    [HasInvertibleExponent Λ S] [HasTateTwist Λ]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
      (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
        ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj (skyscraperZero Λ n S))) := by
  obtain ⟨e⟩ := nonempty_iso_affineFourierTransform_unit Λ n S Ψ hΨ
  -- `p₁^* Λ ⊗ᴸ 𝒦_ψ ≅ 𝒦_ψ`
  let c : ((derivedTensor (ModuleCat.{u + 1} Λ) _).obj
        ((D((pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj
          (𝟙_ _))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)) :=
    ((derivedTensor (ModuleCat.{u + 1} Λ) _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ _).symm.app (𝟙_ _) ≪≫
        leftDerivedUpperStarConstantComplexIso Λ _)).app _ ≪≫ λ_ _
  let e' : (shiftFunctor _ (Fintype.card n : ℤ)).obj
        ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))) ≅
      (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
        ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj (skyscraperZero Λ n S)) :=
    (shiftFunctor _ _).mapIso
      ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).mapIso c.symm) ≪≫ e
  exact ⟨(shiftFunctorCompIsoId _ (Fintype.card n : ℤ) _ (add_neg_cancel _)).symm.app _ ≪≫
    (shiftFunctor _ _).mapIso e' ≪≫ (shiftFunctorAdd' _ _ _ _ (by ring)).symm.app _⟩

/-- Pulling back a skyscraper along a cartesian square gives a pushforward: for a cartesian
square of schemes

```
    W ───δ───▶ P
    │          │
   π│          │ d
    ▼          ▼
    S ───z───▶ V
```

with `z` and `δ` proper, every twist `m` and shift `a`,

`d^*((z_* Λ)(m)[a]) ≅ (δ_* Λ(m))[a]`.

This is compact-support base change for `z` (`z_* = z_!`), followed by the projection formula
for `δ`.

Class: torsion; decided by compact-support base change and the projection formula at finite
coefficients, which need `[Finite Λ]`.
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_leftDerivedUpperStar_tateTwist_of_isPullback [Finite Λ] [HasTateTwist Λ]
    {S W P V : Scheme.{u}} {π : W ⟶ S} {δ : W ⟶ P} {z : S ⟶ V} {d : P ⟶ V}
    (hsq : IsPullback π δ z d) [IsProper z] [IsProper δ] (m a : ℤ) :
    Nonempty ((L((d)^*[ModuleCat.{u + 1} Λ])).obj
        ((shiftFunctor _ a).obj ((tateTwist Λ V m).obj
          ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)))) ≅
      (shiftFunctor _ a).obj ((R((δ)_*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ W m))) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hsq
  have := isIso_projectionMap_of_finite Λ δ
  -- `d^* z_* Λ ≅ δ_! Λ`, by base change for `z`
  let a₁ : (L((d)^*[ModuleCat.{u + 1} Λ])).obj ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ≅
      (R(δ)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) :=
    (L((d)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ z).symm.app (𝟙_ _)) ≪≫
      (asIso (rightDerivedLowerShriekBaseChangeMap _ hsq)).app (𝟙_ _) ≪≫
      (R(δ)_![ModuleCat.{u + 1} Λ]).mapIso (leftDerivedUpperStarConstantComplexIso Λ π)
  -- `d^*(z_* Λ ⊗ᴸ Λ(m)) ≅ δ_! Λ ⊗ᴸ Λ(m) ≅ δ_!(δ^* Λ(m)) ≅ δ_* Λ(m)`
  let a₂ : (L((d)^*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ V m).obj ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _))) ≅
      (R((δ)_*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ W m) :=
    leftDerivedUpperStarTensorIso _ d _ _ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) _).mapIso a₁).app _ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) _).obj _).mapIso
        (leftDerivedUpperStarTateObjectIso d m) ≪≫
      ((asIso (projectionMap _ δ)).app (𝟙_ _)).app _ ≪≫
      (R(δ)_![ModuleCat.{u + 1} Λ]).mapIso
        (((derivedTensor (ModuleCat.{u + 1} Λ) _).obj (𝟙_ _)).mapIso
          (leftDerivedUpperStarTateObjectIso δ m) ≪≫ λ_ _) ≪≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ _).app _
  exact ⟨((L((d)^*[ModuleCat.{u + 1} Λ])).commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso a₂⟩

omit [Fintype n] in
/-- Pulling the skyscraper at the origin back along the subtraction `(x, y) ↦ x - y` gives the
constant sheaf on the diagonal: for every twist `m` and shift `a`,

`sub^*(δ₀(m)[a]) ≅ (Δ_* Λ(m))[a]`,

since the diagonal is the fibre of the subtraction over the zero section
(`AlgebraicGeometry.AffineSpace.isPullback_diagonal_sub`).
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_leftDerivedUpperStar_sub_skyscraperZero [Finite Λ] [HasTateTwist Λ]
    (m a : ℤ) :
    Nonempty ((L((sub n S)^*[ModuleCat.{u + 1} Λ])).obj
        ((shiftFunctor _ a).obj ((tateTwist Λ (𝔸(n; S)) m).obj (skyscraperZero Λ n S))) ≅
      (shiftFunctor _ a).obj
        ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ (𝔸(n; S)) m))) :=
  -- The target of the diagonal is `pullback.diagonalObj`; naming it `pullback` here keeps the
  -- derived tensor products over a single scheme, which the kernel compares much faster.
  nonempty_iso_leftDerivedUpperStar_tateTwist_of_isPullback Λ
    (P := pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) (isPullback_diagonal_sub n S) m a

/-- The compactly supported direct image of an integrand of Artin–Schreier sheaves along a
cartesian square: for a cartesian square

```
    T ───σ───▶ P
    │          │
 r₁₃│          │ p₂
    ▼          ▼
    Q ───d───▶ V
```

of schemes of characteristic `p`, two maps `r₁₂, r₂₃ : T ⟶ P`, a function `b` on `P` and two
characters `ψ, ψ'` such that `r₁₂^* ℒ_{ψ, b} ⊗ r₂₃^* ℒ_{ψ', b} ≅ σ^* ℒ_{ψ, b}`,

`Rr₁₃,!(r₁₂^* ℒ_{ψ, b} ⊗ᴸ r₂₃^* ℒ_{ψ', b}) ≅ d^* Rp₂,! ℒ_{ψ, b}`.

The derived tensor product is computed on sheaves, Artin–Schreier sheaves being flat, and
compact-support base change concludes. The sheaves are passed as `F`, `F'` together with
equations, so that the statement can be applied to sheaves that are only definitionally
Artin–Schreier sheaves, such as the Fourier kernels.

Class: torsion; decided by compact-support base change, which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_rightDerivedLowerShriek_artinSchreierSheafZMod_of_isPullback [Finite Λ]
    {T P Q V : Scheme.{u}} [CharP Γ(P, ⊤) p] [CharP Γ(T, ⊤) p]
    (r₁₂ r₂₃ σ : T ⟶ P) (r₁₃ : T ⟶ Q) (p₂ : P ⟶ V) (d : Q ⟶ V)
    (hsq : IsPullback σ r₁₃ p₂ d) [HasCompactification p₂] [HasCompactification r₁₃]
    [QuasiCompact r₁₃] (Ψ Ψ' : AddChar (ZMod p) Λ) (b : Γ(P, ⊤))
    (hm : Nonempty (artinSchreierSheafZMod T Ψ (r₁₂.appTop b) ⊗
      artinSchreierSheafZMod T Ψ' (r₂₃.appTop b) ≅ artinSchreierSheafZMod T Ψ (σ.appTop b)))
    (F F' : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : F = artinSchreierSheafZMod P Ψ b) (hF' : F' = artinSchreierSheafZMod P Ψ' b) :
    Nonempty ((R(r₁₃)_![ModuleCat.{u + 1} Λ]).obj
        ((derivedTensorRight (ModuleCat.{u + 1} Λ) T
          ((D((r₂₃)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F'))).obj
          ((D((r₁₂)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (L((d)^*[ModuleCat.{u + 1} Λ])).obj ((R(p₂)_![ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  subst hF hF'
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hsq
  obtain ⟨m⟩ := hm
  -- the integrand is the pullback of `ℒ_{ψ, b}` along `σ`
  let k : (derivedTensorRight (ModuleCat.{u + 1} Λ) T
          ((D((r₂₃)^*[ModuleCat.{u + 1} Λ])).obj
            ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod P Ψ' b)))).obj
          ((D((r₁₂)^*[ModuleCat.{u + 1} Λ])).obj
            ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod P Ψ b))) ≅
      (D((σ)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod P Ψ b)) :=
    (derivedTensorRight (ModuleCat.{u + 1} Λ) T _).mapIso
        (((r₁₂)^*[ModuleCat.{u + 1} Λ].mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (artinSchreierSheafZModPullbackIso r₁₂ Ψ b)) ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj _).mapIso
        (((r₂₃)^*[ModuleCat.{u + 1} Λ].mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (artinSchreierSheafZModPullbackIso r₂₃ Ψ' b)) ≪≫
      derivedTensorSingleIsoOfFlat _ _ (flat_artinSchreierSheafZMod T Ψ' _) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (m ≪≫ (artinSchreierSheafZModPullbackIso σ Ψ b).symm) ≪≫
      (((σ)^*[ModuleCat.{u + 1} Λ].mapDerivedCategorySingleFunctor 0).app _).symm
  exact ⟨(R(r₁₃)_![ModuleCat.{u + 1} Λ]).mapIso
      (k ≪≫ (leftDerivedUpperStarIsoMapDerivedCategory _ σ).symm.app _) ≪≫
    (asIso (rightDerivedLowerShriekBaseChangeMap _ hsq)).symm.app _⟩

omit [Fact p.Prime] [Fintype n] in
/-- The triple product `𝔸(n; S) ×_S 𝔸(n; S) ×_S 𝔸(n; S)` has characteristic `p` if
`𝔸(n; S) ×_S 𝔸(n; S)` does: it maps to it by `r₁₂` and has a section over it. -/
theorem charP_appTop_tripleProduct [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p] :
    CharP Γ(pullback (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)), ⊤) p := by
  let σ : pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ⟶
      pullback (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
        (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
    pullback.lift (𝟙 _) (pullback.lift (pullback.snd _ _) (pullback.snd _ _) rfl)
      (by rw [pullback.lift_fst, Category.id_comp])
  refine ⟨fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · have h' := congrArg σ.appTop h
    rw [map_natCast, map_zero] at h'
    exact (CharP.cast_eq_zero_iff _ p x).1 h'
  · have h' := congrArg (pullback.fst (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))).appTop
        ((CharP.cast_eq_zero_iff _ p x).2 h)
    rwa [map_natCast, map_zero] at h'

/-- The convolution of the Fourier kernels of `ψ` and `ψ⁻¹` is the pullback along the
subtraction `(x, y) ↦ x - y` of the compactly supported direct image of the Fourier kernel:

`𝒦_{ψ⁻¹} ∗ 𝒦_ψ ≅ sub^* Rp₂,! 𝒦_ψ`.

On the triple product the integrand `r₁₂^* 𝒦_ψ ⊗ᴸ r₂₃^* 𝒦_{ψ⁻¹}` is the Artin–Schreier sheaf
of `⟨x, ξ⟩ - ⟨ξ, y⟩ = ⟨ξ, x - y⟩`, the pullback of `𝒦_ψ` along the shear
`(x, ξ, y) ↦ (ξ, x - y)`, which exhibits `r₁₃` as a base change of `p₂` along the subtraction
(`AlgebraicGeometry.AffineSpace.isPullback_convolutionShear`).

Class: torsion; decided by compact-support base change, which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_kernelConvolution_fourierKernel [Finite Λ]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    [HasCompactification
      (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (kernelConvolution (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S))) ≅
        (L((sub n S)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))))) := by
  have := charP_appTop_tripleProduct n S (p := p)
  have hsq := isPullback_convolutionShear (sub n S) (sub_over n S)
  have : QuasiCompact (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have hm := nonempty_iso_artinSchreierSheafZMod_sub _ Ψ
    ((pullback.fst (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))).appTop (stdPairing n S))
    ((pullback.snd (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))).appTop (stdPairing n S))
  rw [← convolutionShear_sub_appTop_stdPairing] at hm
  -- unfolding `kernelConvolution` here directly is very slow in the kernel
  rw [kernelConvolution_eq]
  exact nonempty_iso_rightDerivedLowerShriek_artinSchreierSheafZMod_of_isPullback Λ _ _ _ _ _ _
    hsq Ψ Ψ⁻¹ _ hm _ _ rfl rfl

/-- The convolution of the Fourier kernel of `ψ` with itself is the pullback along the addition
`(x, y) ↦ x + y` of the compactly supported direct image of the Fourier kernel:

`𝒦_ψ ∗ 𝒦_ψ ≅ add^* Rp₂,! 𝒦_ψ`.

On the triple product the integrand is the Artin–Schreier sheaf of `⟨x, ξ⟩ + ⟨ξ, y⟩`, the
pullback of `𝒦_ψ` along the shear `(x, ξ, y) ↦ (ξ, x + y)`.

Class: torsion; decided by compact-support base change, which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_kernelConvolution_fourierKernel_self [Finite Λ]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    [HasCompactification
      (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (kernelConvolution (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
        (L((add n S)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))))) := by
  have := charP_appTop_tripleProduct n S (p := p)
  have hsq := isPullback_convolutionShear (add n S) (add_over n S)
  have : QuasiCompact (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have hm := nonempty_iso_artinSchreierSheafZMod_add _ Ψ
    ((pullback.fst (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))).appTop (stdPairing n S))
    ((pullback.snd (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))).appTop (stdPairing n S))
  rw [← convolutionShear_add_appTop_stdPairing] at hm
  -- unfolding `kernelConvolution` here directly is very slow in the kernel
  rw [kernelConvolution_eq]
  exact nonempty_iso_rightDerivedLowerShriek_artinSchreierSheafZMod_of_isPullback Λ _ _ _ _ _ _
    hsq Ψ Ψ _ hm _ _ rfl rfl

omit [Fintype n] in
/-- Pulling the skyscraper at the origin back along the addition `(x, y) ↦ x + y` gives the
constant sheaf on the anti-diagonal: for every twist `m` and shift `a`,

`add^*(δ₀(m)[a]) ≅ ((id × ι)_* Δ_* Λ(m))[a]`,

since the anti-diagonal is the fibre of the addition over the zero section
(`AlgebraicGeometry.AffineSpace.isPullback_diagonal_negSnd_add`).
(sketch blueprint: `sk-prop-convolution-kernel`, proof) -/
theorem nonempty_iso_leftDerivedUpperStar_add_skyscraperZero [Finite Λ] [HasTateTwist Λ]
    (m a : ℤ) :
    Nonempty ((L((add n S)^*[ModuleCat.{u + 1} Λ])).obj
        ((shiftFunctor _ a).obj ((tateTwist Λ (𝔸(n; S)) m).obj (skyscraperZero Λ n S))) ≅
      (shiftFunctor _ a).obj ((R((negSnd n S)_*[ModuleCat.{u + 1} Λ])).obj
        ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ (𝔸(n; S)) m)))) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_tateTwist_of_isPullback Λ
    (P := pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) (isPullback_diagonal_negSnd_add n S) m a
  exact ⟨e ≪≫ (shiftFunctor _ a).mapIso
    ((rightDerivedLowerStarComp _ (pullback.diagonal (𝔸(n; S) ↘ S)) (negSnd n S)).symm.app _)⟩


end ConvolutionKernel

section Inversion

variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
variable [HasCompactification
  (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The convolution of the kernel of `FT_{ψ⁻¹}` with the kernel of `FT_ψ` on `𝔸(n; S)` is
the delta kernel `Δ_* Λ(-r)[-2r]` supported on the diagonal, `r = #n` being the relative
dimension. The companion statement for the same character is
`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution_self`.

The proof: the convolution is `sub^* Rp₂,! 𝒦_ψ` for the subtraction `(x, y) ↦ x - y`
(`AlgebraicGeometry.Etale.nonempty_iso_kernelConvolution_fourierKernel`), `Rp₂,! 𝒦_ψ` is
`δ₀(-r)[-2r]` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_fourierKernel`),
and `sub^* δ₀` is the constant sheaf on the diagonal
(`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sub_skyscraperZero`).

The character must be **nontrivial** in the strong sense that
`Ψ 1 - 1` is a unit of `Λ`, which is what makes `H_c^*(𝔸¹, ℒ_ψ)` vanish: for `Ψ = 1` both
kernels are constant and the convolution is `Λ(-r)[-2r]`, supported everywhere, and `Ψ ≠ 1`
is not enough when `Λ` is not a domain
(see `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`).

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-prop-convolution-kernel`) -/
theorem nonempty_iso_fourierKernel_convolution [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (kernelConvolution (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S))) ≅
        (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
          ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))) := by
  obtain ⟨e₁⟩ := nonempty_iso_kernelConvolution_fourierKernel Λ n S Ψ
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerShriek_fourierKernel Λ n S Ψ hΨ
  obtain ⟨e₃⟩ := nonempty_iso_leftDerivedUpperStar_sub_skyscraperZero Λ n S
    (-(Fintype.card n : ℤ)) (-2 * (Fintype.card n : ℤ))
  exact ⟨e₁ ≪≫ (L((sub n S)^*[ModuleCat.{u + 1} Λ])).mapIso e₂ ≪≫ e₃⟩

/-- The convolution of the kernel of `FT_ψ` with itself on `𝔸(n; S)` is the delta kernel of the
anti-diagonal, `(id × ι)_* Δ_* Λ(-r)[-2r]`, `ι` being the reflection `x ↦ -x` and `r = #n`
the relative dimension: the computation of
`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution` with `x - y` replaced by
`x + y`, whose vanishing locus is the anti-diagonal.

The character must be nontrivial in the strong sense that `Ψ 1 - 1` is a unit of `Λ`, as in
`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`.

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-prop-convolution-kernel`) -/
theorem nonempty_iso_fourierKernel_convolution_self [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (kernelConvolution (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
        (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
          ((R((negSnd n S)_*[ModuleCat.{u + 1} Λ])).obj
            ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
              (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ)))))) := by
  obtain ⟨e₁⟩ := nonempty_iso_kernelConvolution_fourierKernel_self Λ n S Ψ
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerShriek_fourierKernel Λ n S Ψ hΨ
  obtain ⟨e₃⟩ := nonempty_iso_leftDerivedUpperStar_add_skyscraperZero Λ n S
    (-(Fintype.card n : ℤ)) (-2 * (Fintype.card n : ℤ))
  exact ⟨e₁ ≪≫ (L((add n S)^*[ModuleCat.{u + 1} Λ])).mapIso e₂ ≪≫ e₃⟩

/-- **Fourier inversion.** On `𝔸(n; S)` the Fourier–Deligne transform for the inverse
character inverts the Fourier–Deligne transform up to the Tate twist `(-r)`,
`r = #n` being the relative dimension:

`FT_{ψ⁻¹} FT_ψ(K) ≅ K(-r)`,

functorially in `K`:

```
                 FT_ψ
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
          (-r)  ╲           │ FT_ψ⁻¹
                  ▶         ▼
                    D(𝔸(n; S))
```

The proof composes the two kernel transforms
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`), computes the convolution of the
kernels (`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`), moves the shift
out of the kernel and recognises the kernel transform of `Δ_* Λ(-r)` as the Tate twist
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`). The hypotheses are those
of the convolution computation: for `Ψ = 1` the transform is `Rp₂,! p₁^*(-)[r]`, which is not
invertible.
The composition law of kernel transforms also needs the projection
`𝔸(n; S) ×ₛ 𝔸(n; S) ×ₛ 𝔸(n; S) ⟶ 𝔸(n; S)` onto the last factor to admit a compactification.

Class: torsion; decided by the convolution computation
`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution` (cohomology of `𝔸^r`), which
needs `[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-thm-inversion`) -/
-- TODO: discharge the `HasCompactification` hypothesis: the composite is a morphism
-- `𝔸^{3n}_S ⟶ 𝔸^n_S`, which is compactified through projective space by
-- `AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`, with no need for Nagata.
theorem nonempty_iso_affineFourierTransform_comp_inv [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ]
    [HasCompactification (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ≫
      pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ⁻¹ ≅
        tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))) := by
  -- The kernel transform depends functorially on the kernel. Tensoring is first mapped over
  -- an arbitrary scheme `X`: doing so directly over the fibre product times out in the kernel.
  have ht {X : Scheme.{u}} {N N' : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (f : N ≅ N') :
      derivedTensorRight (ModuleCat.{u + 1} Λ) X N ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) X N' :=
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso f
  have hk {𝒦 𝒦' : DerivedCategory (Sheaf (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (e : 𝒦 ≅ 𝒦') (a : ℤ) :
      kernelTransform (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) 𝒦 a ≅
        kernelTransform (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) 𝒦' a :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (ht e) _)
  obtain ⟨e₁⟩ := nonempty_iso_kernelTransform_comp Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
    (𝔸(n; S) ↘ S) ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
    ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S)))
    (Fintype.card n) (Fintype.card n)
  obtain ⟨e₂⟩ := nonempty_iso_fourierKernel_convolution Λ n S Ψ hΨ
  obtain ⟨e₃⟩ := nonempty_iso_kernelTransform_shift (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S)
    (𝔸(n; S) ↘ S)
    ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
      (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))
    (-2 * (Fintype.card n : ℤ)) (Fintype.card n + Fintype.card n)
  obtain ⟨e₄⟩ := nonempty_iso_kernelTransform_diagonal Λ (𝔸(n; S) ↘ S)
    (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ)))
  have hr : -2 * (Fintype.card n : ℤ) + (Fintype.card n + Fintype.card n) = 0 := by ring
  exact ⟨e₁ ≪≫ hk e₂ _ ≪≫ e₃ ≪≫
    eqToIso (congrArg (kernelTransform (ModuleCat.{u + 1} Λ) _ _ _) hr) ≪≫ e₄⟩

/-- Applying the Fourier–Deligne transform twice with the *same* character gives back the
reflection `ι^* K` of the input, Tate twisted by `(-r)`:

`FT_ψ FT_ψ(K) ≅ ι^* K(-r)`,

functorially in `K`, where `ι = AlgebraicGeometry.AffineSpace.neg` is `x ↦ -x`:

```
                 FT_ψ
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
     ι^* ⋙ (-r) ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

It follows from `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`, which
gives `FT_ψ ≅ ι^* ⋙ FT_{ψ⁻¹}`, and inversion
(`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv`) for `ψ⁻¹`; the
hypotheses are those of inversion.

Class: torsion; decided by inversion
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-thm-inversion`) -/
theorem nonempty_iso_affineFourierTransform_comp_self [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ]
    [HasCompactification (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ≫
      pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙
          tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))) := by
  have h : Ψ⁻¹ 1 * Ψ 1 = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hΨ' : IsUnit (Ψ⁻¹ 1 - 1) := by
    rw [show Ψ⁻¹ 1 - 1 = -Ψ⁻¹ 1 * (Ψ 1 - 1) by linear_combination h]
    exact (IsUnit.of_mul_eq_one _ h).neg.mul hΨ
  obtain ⟨s⟩ := nonempty_iso_affineFourierTransform_inv Λ n S Ψ⁻¹
  obtain ⟨i⟩ := nonempty_iso_affineFourierTransform_comp_inv Λ n S Ψ⁻¹ hΨ'
  rw [inv_inv] at s i
  exact ⟨Functor.isoWhiskerRight s _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ i⟩

end Inversion

end AlgebraicGeometry.Etale
