/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.FourierTransform.Properties
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!

# The Fourier–Deligne transform on affine space

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is stated for an
arbitrary pair of `S`-schemes with a pairing. Its main case is affine `n`-space `𝔸(n; S)`
paired with itself by the standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative
dimension `r = #n`; this file records that datum and the computation of the transform of
the two simplest complexes, the constant sheaf and the skyscraper at the origin.

The affine-space data themselves — the standard pairing, the zero section and the
reflection `x ↦ -x` — are in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`; they have nothing to do with étale
sheaves.

## Main definitions

- `AlgebraicGeometry.Etale.affineFourierTransform`: the Fourier–Deligne transform of
  `𝔸(n; S)` with the standard pairing.
- `AlgebraicGeometry.Etale.skyscraperZero`: the skyscraper `δ₀` at the origin.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_skyscraperZero`: the transform
  exchanges the constant sheaf and the skyscraper at the origin.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`: the transform for the
  inverse character is the transform of the reflected input.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The statements only assert that an isomorphism *exists*. Later uses will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

The transform of the constant sheaf vanishes off the origin: its stalk at a geometric point
`ξ ≠ 0` is `RΓ_c(𝔸ʳ_Ω, ℒ_{ψ(⟨x, ξ⟩)})[r]` by the stalk formula
(`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`), which vanishes
(`AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_pairingAt`),
and geometric points detect vanishing. A complex vanishing off the origin is the pushforward of
its restriction to the origin (supported localization), and that restriction is
`Rπ_! Λ [r] ≅ Λ(-r)[-2r][r]` by compact-support base change along the zero section and
`H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_affineSpace`), which needs
`Λ` finite with exponent invertible on `S`. The twist `(-r)` is moved onto the
skyscraper by the projection formula for the zero section
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerStar_of_finite`). The
transform of the skyscraper is computed by proper base change of `δ₀` along `p₁`, which gives
the constant sheaf on the slice `s : {0} ×_S 𝔸(n; S) ⟶ 𝔸(n; S) ×_S 𝔸(n; S)`, the projection
formula for the closed immersion `s`, on whose image the kernel is trivial, and
`Rp₂,! Rs_* = R(s ≫ p₂)_! = R(𝟙)_!`.
The comparison of the transforms for `ψ` and `ψ⁻¹` is base change of `Rp₂,!` along the
isomorphism `ι × 1`; it compares the chosen compactifications of `p₂` and of its conjugate by
`ι × 1`.

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
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of affine `n`-space over `S`: the transform of
`AlgebraicGeometry.Etale.fourierTransform` for `𝔸(n; S)` paired with itself by the standard
pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative dimension `r = #n`. On the affine
line this is `FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ℒ_{ψ(xξ)})[1]`. -/
noncomputable def affineFourierTransform (Ψ : AddChar (ZMod p) Λ) :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) (Fintype.card n)

/-- The skyscraper `δ₀` at the origin of `𝔸(n; S)`: the direct image of the constant sheaf
`Λ` along the zero section. -/
noncomputable def skyscraperZero :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)


section FirstFormula

/-! ### Auxiliary computations for the first Fourier formula -/

omit [Fintype n] [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
  [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))] in
/-- The geometric fibre `𝔸(n; S) ×_S Ω` of `𝔸(n; S)` over a point `ξ : Spec Ω ⟶ 𝔸(n; S)` has
characteristic `p`: it is nonempty and receives a ring map from `Γ(𝔸(n; S) ×_S 𝔸(n; S))`. -/
theorem charP_appTop_pullback_comp {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ 𝔸(n; S))
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p] :
    CharP Γ(pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S), ⊤) p := by
  let a : Spec (.of Ω) ⟶ pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S) :=
    pullback.lift (ξ ≫ 𝔸(n; S) ↘ S ≫ zeroSection n S) (𝟙 _) (by simp)
  have : Nonempty (⊤ : (pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S)).Opens) :=
    ⟨⟨a.base default, trivial⟩⟩
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
  let ψ : pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S) ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ) (by simp [pullback.condition])
  rw [← map_natCast ψ.appTop.hom, CharP.cast_eq_zero, map_zero]

omit [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
  [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))] in
/-- Blueprint `sk-prop-first-formula`, the case `ξ ≠ 0` of its proof: for a geometric point
`ξ : Spec Ω ⟶ 𝔸(n; S)` off the zero section, with `Ω` separably closed, and a character with
`Ψ 1 - 1` a unit, the compactly supported cohomology of the geometric fibre `𝔸ⁿ_Ω` with
coefficients in the Artin–Schreier sheaf of the nonzero linear form `x ↦ ⟨x, ξ⟩` vanishes:

`RΓ_c(𝔸ⁿ_Ω, ℒ_{ψ(⟨x, ξ⟩)}) = 0`.

After a linear change of coordinates the form is the first coordinate, and by Künneth this is
`RΓ_c(𝔸¹_Ω, ℒ_ψ) ⊗ᴸ RΓ_c(𝔸ⁿ⁻¹_Ω, Λ)`, whose first factor vanishes: by duality on the curve
`𝔸¹` (`sk-thm-derived-duality`) it is dual to `RΓ(𝔸¹_Ω, ℒ_{ψ⁻¹})(1)`, which vanishes for a
nontrivial character (`sk-lem-as-properties`). -/
theorem isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_pairingAt [Finite Λ]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ 𝔸(n; S)) (hξ : ∃ i, ξ.appTop (coord S i) ≠ 0)
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S), ⊤) p] :
    IsZero ((R(pullback.snd (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod _ Ψ
        (pairingAt (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (stdPairing n S) ξ)))) :=
  sorry

/-- The stalk of `FT_ψ(Λ)` at a geometric point `ξ` off the zero section vanishes: by the stalk
formula it is `RΓ_c(𝔸ⁿ_Ω, ℒ_{ψ(⟨x, ξ⟩)})[r]`, which vanishes by
`AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_pairingAt`. -/
theorem isZero_upperStar_affineFourierTransform_unit [Finite Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : IsUnit (Ψ 1 - 1)) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ 𝔸(n; S))
    (hξ : ∃ i, ξ.appTop (coord S i) ≠ 0)
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S), ⊤) p] :
    IsZero ((D((ξ)^*[ModuleCat.{u + 1} Λ])).obj
      ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _))) := by
  obtain ⟨e⟩ := nonempty_iso_fourierTransform_geometricStalk Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ
    (stdPairing n S) (Fintype.card n) ξ
  have hA : IsZero ((R(pullback.snd (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
      ((artinSchreierTwist Λ _ Ψ (pairingAt (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (stdPairing n S) ξ)).obj
        ((D((pullback.fst (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj
          (𝟙_ _)))) := by
    have h₀ := isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_pairingAt Λ n S Ψ hΨ ξ hξ
    obtain ⟨u₁⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ)
      (pullback.fst (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S))
    exact h₀.of_iso ((R(_)_![_]).mapIso
      (((-⊗ᴸ-(_)[_]).mapIso (((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
        u₁)).app _ ≪≫ derivedTensorLeftUnitor _ _ _))
  exact IsZero.of_iso (Functor.map_isZero (shiftFunctor _ (Fintype.card n : ℤ)) hA) (e.app (𝟙_ _))

/-- `FT_ψ(Λ)` vanishes off the origin: its restriction to the open complement `j : U ⟶ 𝔸(n; S)`
of the zero section is zero, since its stalks at all geometric points of `U` vanish
(`AlgebraicGeometry.Etale.isZero_upperStar_affineFourierTransform_unit`). -/
theorem isZero_leftDerivedUpperStar_affineFourierTransform_unit [Finite Λ]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) {U : Scheme.{u}} (j : U ⟶ 𝔸(n; S))
    (hj : Set.range j.base = (Set.range (zeroSection n S).base)ᶜ) :
    IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj
      ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _))) := by
  refine isZero_of_isZero_leftDerivedUpperStar_algClosurePoint Λ _ fun x ↦ ?_
  have := charP_appTop_pullback_comp (p := p) n S (U.algClosurePoint x ≫ j)
  have hξ := exists_appTop_coord_ne_zero (U.algClosurePoint x ≫ j) default
    (by rw [← Set.mem_compl_iff, ← hj]; exact ⟨(U.algClosurePoint x).base default, by simp⟩)
  exact ((isZero_upperStar_affineFourierTransform_unit Λ n S Ψ hΨ _ hξ).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _)).of_iso
    ((leftDerivedUpperStarComp _ (U.algClosurePoint x) j).app _).symm

/-- The restriction of `FT_ψ(Λ)` to the origin is `Rπ_! Λ [r]`: by compact-support base change
along the zero section, it is the compactly supported cohomology of the slice
`𝔸(n; S) ×_S {0}`, on which the kernel is trivial. -/
theorem nonempty_iso_leftDerivedUpperStar_zeroSection_affineFourierTransform_unit [Finite Λ]
    (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((L((zeroSection n S)^*[ModuleCat.{u + 1} Λ])).obj
      ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _)) ≅
      ((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))⟦(Fintype.card n : ℤ)⟧) := by
  have sq := isPullback_zeroRight n S
  have h₁ := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨u₁⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ)
    (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
  obtain ⟨u₂⟩ := nonempty_iso_upperStar_artinSchreierSheafZMod_of_appTop_eq_zero
    (zeroRight n S) Ψ (stdPairing n S)
    (appTop_stdPairing_of_snd_eq n S _ (𝔸(n; S) ↘ S) (zeroRight_snd n S))
  let I := (fourierIntegrand Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)).obj (𝟙_ _)
  let e : (L((zeroRight n S)^*[ModuleCat.{u + 1} Λ])).obj I ≅ 𝟙_ _ :=
    (L((zeroRight n S)^*[_])).mapIso
      (((-⊗ᴸ-(_)[_]).mapIso (((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
        u₁)).app _ ≪≫ derivedTensorLeftUnitor _ _ _) ≪≫
      (singleFunctorCompLeftDerivedUpperStarIso _ _).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso u₂ ≪≫ singleUnitIso Λ _
  exact ⟨((L((zeroSection n S)^*[_])).commShiftIso (Fintype.card n : ℤ)).app
      ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj I) ≪≫
      (shiftFunctor _ _).mapIso ((asIso (rightDerivedLowerShriekBaseChangeMap _ sq)).app I ≪≫
        (R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).mapIso e)⟩

omit [Fintype n] [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
  [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))] in
/-- The Tate twist of the skyscraper is the pushforward of the twist on the base,
`δ₀(m) ≅ Rz_* Λ_S(m)`, by the projection formula for the closed immersion `z`. -/
theorem nonempty_iso_tateTwist_skyscraperZero [Finite Λ] [HasTateTwist Λ] (m : ℤ) :
    Nonempty ((tateTwist Λ (𝔸(n; S)) m).obj (skyscraperZero Λ n S) ≅
      R((zeroSection n S)_*[ModuleCat.{u + 1} Λ]).obj (tateObject Λ S m)) := by
  obtain ⟨pf⟩ := nonempty_iso_derivedTensor_rightDerivedLowerStar_of_finite Λ
    (zeroSection n S) (𝟙_ _) (tateObject Λ (𝔸(n; S)) m)
  exact ⟨pf ≪≫
      R((_)_*[_]).mapIso (((-⊗ᴸ-(_)[_]).obj _).mapIso (leftDerivedUpperStarTateObjectIso _ _) ≪≫
        derivedTensorLeftUnitor _ _ _)⟩

omit [Fintype n] [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
  [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))] in
/-- The pullback of the skyscraper to `𝔸(n; S) ×_S 𝔸(n; S)` along the first projection is the
constant sheaf on the slice `{0} ×_S 𝔸(n; S)`, by proper base change along the zero section. -/
theorem nonempty_iso_leftDerivedUpperStar_skyscraperZero [Finite Λ] :
    Nonempty (D((pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))^*[ModuleCat.{u + 1} Λ]).obj
      (skyscraperZero Λ n S) ≅ R((zeroLeft n S)_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  have sq := isPullback_zeroLeft n S
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    sq.flip
  obtain ⟨u₁⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S)
  exact ⟨((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
      (asIso (derivedBaseChangeMap _ sq.flip.toCommSq)).app (𝟙_ _) ≪≫ R((_)_*[_]).mapIso u₁⟩

omit [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))] in
/-- The kernel is trivial on the slice `{0} ×_S 𝔸(n; S)`, so tensoring the constant sheaf of
the slice with it does nothing: `Rs_* Λ ⊗ᴸ 𝒦_ψ ≅ Rs_* Λ` for `s` the inclusion of the slice,
by the projection formula for the closed immersion `s`. -/
theorem nonempty_iso_derivedTensor_fourierKernel_zeroLeft [Finite Λ]
    (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (((-⊗ᴸ-(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))[ModuleCat.{u + 1} Λ]).obj
      (R((zeroLeft n S)_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _))).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
        R((zeroLeft n S)_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  have hs : IsClosedImmersion (zeroLeft n S) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_zeroLeft n S).flip
      inferInstance
  obtain ⟨u₂⟩ := nonempty_iso_upperStar_artinSchreierSheafZMod_of_appTop_eq_zero
    (zeroLeft n S) Ψ (stdPairing n S)
    (appTop_stdPairing_of_fst_eq n S _ (𝔸(n; S) ↘ S) (zeroLeft_fst n S))
  obtain ⟨pf⟩ := nonempty_iso_derivedTensor_rightDerivedLowerStar_of_finite Λ
    (zeroLeft n S) (𝟙_ _) ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
  exact ⟨pf ≪≫
      R((_)_*[_]).mapIso (((-⊗ᴸ-(_)[_]).obj _).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso _ _).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso u₂ ≪≫ singleUnitIso Λ _) ≪≫
        derivedTensorLeftUnitor _ _ _)⟩

end FirstFormula

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` is the skyscraper at
the origin of the dual, Tate twisted and shifted by the relative dimension `r = #n`:

`FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(Λ) ≅ δ₀(-1)[-1]`.

The character must be **nontrivial** in the strong sense that `Ψ 1 - 1` is a unit of `Λ`:
the proof uses `H_c^*(𝔸¹, ℒ_ψ) = 0`, and the `ψ`-isotypic part of `H_c^*(𝔸¹, Λ)` is killed
by `Ψ 1 - 1`. For `Ψ = 1` the kernel is the constant sheaf and the transform of `Λ` is
`Λ(-r)[-r]`, supported everywhere. Asking `Ψ ≠ 1` is not enough when `Λ` is not a domain:
for `Λ = 𝔽_ℓ × 𝔽_ℓ` and `Ψ = (ψ₀, 1)` the transform has the trivial-character transform as a
factor.

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_affineFourierTransform_unit [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _) ≅
        (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
          ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
            (skyscraperZero Λ n S))) := by
  let z := zeroSection n S
  -- the open complement of the origin
  let U : (𝔸(n; S)).Opens :=
    ⟨(Set.range z.base)ᶜ, z.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι.base = (Set.range z.base)ᶜ := Scheme.Opens.range_ι U
  -- the transform of `Λ` is supported at the origin
  obtain ⟨e₀⟩ := nonempty_iso_rightDerivedLowerStar_leftDerivedUpperStar_of_isZero Λ z U.ι
    (by rw [hU, compl_compl]) _
    (isZero_leftDerivedUpperStar_affineFourierTransform_unit Λ n S Ψ hΨ U.ι hU)
  -- its restriction to the origin is `Rπ_! Λ [r] ≅ Λ(-r)[-2r][r]`
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_zeroSection_affineFourierTransform_unit Λ n S Ψ
  obtain ⟨a⟩ := nonempty_iso_rightDerivedLowerShriek_affineSpace Λ n S
  obtain ⟨e₃⟩ := nonempty_iso_tateTwist_skyscraperZero Λ n S (-(Fintype.card n : ℤ))
  exact ⟨e₀ ≪≫ R((z)_*[_]).mapIso (e₁ ≪≫ (shiftFunctor _ _).mapIso
      ((R(_)_![_]).mapIso (constantComplexIsoUnit Λ _).symm ≪≫ a) ≪≫
      (shiftFunctorAdd' _ (-(2 * Fintype.card n : ℤ)) (Fintype.card n) (-(Fintype.card n : ℤ))
        (by omega)).symm.app _) ≪≫
    (R((z)_*[_]).commShiftIso (-(Fintype.card n : ℤ))).app _ ≪≫
    (shiftFunctor _ _).mapIso e₃.symm⟩

/-- The Fourier–Deligne transform of the skyscraper at the origin of `𝔸(n; S)` is the
constant sheaf, shifted by the relative dimension `r = #n`:

`FT_ψ(δ₀) ≅ Λ[r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(δ₀) ≅ Λ[1]`. Unlike
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` this holds for every
character: the kernel restricted to `{0} ×_S 𝔸(n; S)` is the Artin–Schreier sheaf of the zero
function.

Class: torsion; decided by compact-support base change of `Rp₂,!` along the zero section,
which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_affineFourierTransform_skyscraperZero [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
        (shiftFunctor _ (Fintype.card n : ℤ)).obj (𝟙_ _)) := by
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_skyscraperZero Λ n S
  obtain ⟨e₂⟩ := nonempty_iso_derivedTensor_fourierKernel_zeroLeft Λ n S Ψ
  let π := 𝔸(n; S) ↘ S
  have : IsClosedImmersion (zeroLeft n S) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_zeroLeft n S).flip
      inferInstance
  have : HasCompactification (zeroLeft n S ≫ pullback.snd π π) := by
    rw [zeroLeft_snd]; infer_instance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp (ModuleCat.{u + 1} Λ) (zeroLeft n S)
    (pullback.snd π π)
  obtain ⟨i⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq_id (ModuleCat.{u + 1} Λ)
    (zeroLeft n S ≫ pullback.snd π π) (zeroLeft_snd n S)
  exact ⟨(shiftFunctor _ _).mapIso ((R(pullback.snd π π)_![_]).mapIso
    (((-⊗ᴸ-(_)[_]).mapIso e₁).app _ ≪≫ e₂ ≪≫
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ (zeroLeft n S)).app _).symm) ≪≫
    (c.app _).symm ≪≫ i.app _)⟩

/-- The Fourier–Deligne transform for the inverse character is the transform of the reflected
input, `ι = AlgebraicGeometry.AffineSpace.neg` being `x ↦ -x`:

`FT_{ψ⁻¹}(K) ≅ FT_ψ(ι^* K)`,

naturally in `K`:

```
                 ι^*
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
        FT_ψ⁻¹  ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

The kernel of `FT_{ψ⁻¹}` is the pullback of the kernel of `FT_ψ` along `ι × 1`, by
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` and `b(-x, ξ) = -b(x, ξ)`.
It holds for every character.

Class: compactification-dependent; decided by independence of the compactification. The
blueprint proof is formal (base change along the isomorphism `ι × 1`); `[Finite Λ]` enters
solely through independence of the compactification
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), comparing the chosen compactifications
of `p₂` and of its conjugate by `ι × 1`.
(sketch blueprint: `sk-def-ft`, remark; `lem-fd-as-lisse`) -/
theorem nonempty_iso_affineFourierTransform_inv [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (affineFourierTransform Λ n S Ψ⁻¹ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙ affineFourierTransform Λ n S Ψ) :=
  sorry

end AlgebraicGeometry.Etale
