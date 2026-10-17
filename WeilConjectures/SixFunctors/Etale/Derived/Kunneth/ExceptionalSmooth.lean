/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons

/-!

# The exceptional Künneth map for smooth morphisms

For smooth separated morphisms `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂` of pure relative dimensions
`d₁`, `d₂` over a base `S` separated of finite type over a field, smooth purity
`Rfᵢ^! ≅ Lfᵢ^*(dᵢ)[2dᵢ]` (`sk-thm-smooth-purity`) turns the exceptional Künneth comparison
`α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)` into the compatibility of the external product
with pullbacks and the additivity of the Tate twists. This is the smooth case of
`prop-trf-exceptional-kunneth`, the first step of its blueprint proof.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek_of_smooth`
  (`prop-trf-exceptional-kunneth`, smooth case).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- A complex of `Dctf` lies in `D^b_{ctf}` in the sense of the purity chapter. -/
lemma boundedConstructibleFiniteTor_of_constructibleFiniteTor {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    boundedConstructibleFiniteTor Λ X K := by
  obtain ⟨hbc, a, b, h⟩ := hK
  exact ⟨hbc, a, b, hasTorAmplitudeIn_of_torAmplitudeIn Λ h⟩

/-- Smooth purity in tensor form: `Rf^! K ≅ Lf^* K ⊗ᴸ Λ_X(d)[2d]`. -/
lemma nonempty_iso_rightDerivedUpperShriek_tensor_tateObject [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj K ≅
      (L((f)^*[ModuleCat.{u + 1} Λ])).obj K ⊗ (tateObject Λ X d)⟦2 * (d : ℤ)⟧) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_twistShift Λ (d := d) f aY K
    (boundedConstructibleFiniteTor_of_constructibleFiniteTor Λ hK)
  exact ⟨e ≪≫ twistShiftObjIso Λ X d _ ≪≫
    ((derivedTensor _ X).obj _).mapIso (twistShiftConstantComplexIso Λ X d)⟩

/-- Blueprint `prop-trf-exceptional-kunneth`: Exceptional Künneth; the `α` map, for smooth
morphisms.

Let `S` be separated and locally of finite type over a field, `b₁ : Y₁ ⟶ S`, `b₂ : Y₂ ⟶ S`
separated and locally of finite type, and `f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` smooth separated of
pure relative dimensions `d₁`, `d₂`. For `N₁ ∈ Dctf(Y₁, Λ)`, `N₂ ∈ Dctf(Y₂, Λ)` with
`N₁ ⊠ N₂ ∈ Dctf`,

`Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)`.

By smooth purity (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift`)
both sides are `(Lf₁^* N₁ ⊠ Lf₂^* N₂) ⊗ Λ(d₁ + d₂)[2(d₁ + d₂)]`: the external product commutes
with pullbacks and the Tate twists add up
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`). -/
theorem nonempty_iso_externalProduct_rightDerivedUpperShriek_of_smooth
    [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k] {S X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (s : S ⟶ Spec (.of k)) [IsSeparated s] [LocallyOfFiniteType s]
    (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) [IsSeparated b₁] [LocallyOfFiniteType b₁]
    [IsSeparated b₂] [LocallyOfFiniteType b₂]
    {d₁ d₂ : ℕ} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [IsSeparated f₁] [IsSeparated f₂]
    [SmoothOfRelativeDimension d₁ f₁] [SmoothOfRelativeDimension d₂ f₂]
    [HasCompactification f₁] [HasCompactification f₂]
    [IsSeparated (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [SmoothOfRelativeDimension (d₁ + d₂) (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [HasInvertibleExponent Λ X₁] [HasInvertibleExponent Λ X₂]
    [HasInvertibleExponent Λ (pullback (f₁ ≫ b₁) (f₂ ≫ b₂))]
    {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁)
    (h₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂)
    (h₁₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (pullback b₁ b₂)
      (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![ModuleCat.{u + 1} Λ]).obj N₁) ((R(f₂)^![ModuleCat.{u + 1} Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (pullback (f₁ ≫ b₁) (f₂ ≫ b₂)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let P := pullback (f₁ ≫ b₁) (f₂ ≫ b₂)
  let p := pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂)
  let q := pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂)
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_tensor_tateObject Λ (d := d₁) f₁ (b₁ ≫ s) h₁
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_tensor_tateObject Λ (d := d₂) f₂ (b₂ ≫ s) h₂
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_tensor_tateObject Λ (d := d₁ + d₂)
    (pullback.mapOverBase f₁ f₂ b₁ b₂) (pullback.fst b₁ b₂ ≫ b₁ ≫ s) h₁₂
  obtain ⟨g⟩ := nonempty_iso_leftDerivedUpperStar_externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ f₁ f₂
    N₁ N₂
  -- the pulled back factors `p^*(Lf₁^* N₁ ⊗ T₁) ≅ p^* Lf₁^* N₁ ⊗ T_P(d₁)`
  let t₁ : (L((p)^*[ModuleCat.{u + 1} Λ])).obj ((L((f₁)^*[ModuleCat.{u + 1} Λ])).obj N₁ ⊗
        (tateObject Λ X₁ d₁)⟦2 * (d₁ : ℤ)⟧) ≅
      (L((p)^*[ModuleCat.{u + 1} Λ])).obj ((L((f₁)^*[ModuleCat.{u + 1} Λ])).obj N₁) ⊗
        (tateObject Λ P d₁)⟦2 * (d₁ : ℤ)⟧ :=
    leftDerivedUpperStarTensorIso _ p _ _ ≪≫
      ((derivedTensor _ P).obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ p d₁)
  let t₂ : (L((q)^*[ModuleCat.{u + 1} Λ])).obj ((L((f₂)^*[ModuleCat.{u + 1} Λ])).obj N₂ ⊗
        (tateObject Λ X₂ d₂)⟦2 * (d₂ : ℤ)⟧) ≅
      (L((q)^*[ModuleCat.{u + 1} Λ])).obj ((L((f₂)^*[ModuleCat.{u + 1} Λ])).obj N₂) ⊗
        (tateObject Λ P d₂)⟦2 * (d₂ : ℤ)⟧ :=
    leftDerivedUpperStarTensorIso _ q _ _ ≪≫
      ((derivedTensor _ P).obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ q d₂)
  let tw : (tateObject Λ P d₁)⟦2 * (d₁ : ℤ)⟧ ⊗ (tateObject Λ P d₂)⟦2 * (d₂ : ℤ)⟧ ≅
      (tateObject Λ P ((d₁ + d₂ : ℕ) : ℤ))⟦2 * ((d₁ + d₂ : ℕ) : ℤ)⟧ :=
    shiftTateObjectAddIso Λ P d₁ d₂ ≪≫ eqToIso (by push_cast; rfl)
  exact ⟨((derivedTensor _ P).mapIso ((L((p)^*[ModuleCat.{u + 1} Λ])).mapIso e₁)).app _ ≪≫
    ((derivedTensor _ P).obj _).mapIso ((L((q)^*[ModuleCat.{u + 1} Λ])).mapIso e₂) ≪≫
    ((derivedTensor _ P).mapIso t₁).app _ ≪≫ ((derivedTensor _ P).obj _).mapIso t₂ ≪≫
    tensorTensorTensorComm _ _ _ _ ≪≫ whiskerLeftIso _ tw ≪≫
    whiskerRightIso g.symm _ ≪≫ e.symm⟩

end Etale

end AlgebraicGeometry
