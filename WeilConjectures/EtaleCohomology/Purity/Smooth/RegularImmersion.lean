/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import WeilConjectures.SixFunctors.Integral.Exact
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing

/-!
# Purity for regular closed immersions

Purity for a regular closed immersion is *not* one of the five moves of the proof of smooth
purity: it is a consequence of smooth purity applied to the two structure morphisms, together
with the co-projection formula for `Ri^!`. The deformation to the normal cone is never applied
to a general regular immersion.

The theorem is stated about the *fundamental class* `[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` of a
regular closed immersion `i : Z ⟶ X` of pure codimension `c`, which is *defined* by gluing
local classes. A *frame* of `Z` (`AlgebraicGeometry.Scheme.Hom.EtaleFrame`), in
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame`, is an étale
`e : U ⟶ X` with functions `f₁, …, f_c` on `U` generating the ideal of `Z ×_X U`; its class
is the cup product with supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` of the Kummer boundaries
(`AlgebraicGeometry.Etale.frameClass`), and `[Z ⊂ X]` is the unique global class restricting
to the frame class on every frame. Its adjoint is the morphism
`cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`.

The statements about the fundamental class assume the rank-one datum with its normalisation,
`[HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]`: without the normalisation the Kummer
classes, and with them the fundamental class, could be zero.

Classes with supports are morphisms `Λ_X ⟶ Ri_! Ri^! L`, with the supported term `Ri_!` of the
supported localization triangle; for the closed immersion `i` it is `Ri_*`. The coefficients
`Λ_X(c)[2c]` are placed inside `Ri^!`: the blueprint's `Ri^! Λ_X(c)[2c]` is
`Ri^! (Λ_X(c)[2c])`, which is `(Ri^! Λ_X)(c)[2c]` by the co-projection formula
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`).

## Main definitions

- `AlgebraicGeometry.Etale.fundamentalClass`: the fundamental class `[Z ⊂ X]`.
- `AlgebraicGeometry.Etale.fundamentalClassMap`: `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedUpperShriek_of_isRegularImmersion`,
  `isLocallyConstantSheaf_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion`,
  `exists_cover_nonempty_iso_homology_zero_rightDerivedUpperShriek_of_isRegularImmersion`:
  clause (a).
- `AlgebraicGeometry.Etale.existsUnique_fundamentalClass`: clause (b), existence and uniqueness
  of the fundamental class.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`: Steps 1–2,
  `Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`.
- `AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass`: clause (d), étale base
  change.

The generation clause (b) and clause (c), `cl_i` is an isomorphism, are in
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso`; flat base change and the
exterior products of clause (d) are in
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange` and
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}

section Purity

variable [Finite Λ]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

Blueprint `thm-pur-regular-immersion-purity` (the detailed form of the same theorem).

**Purity for a regular closed immersion.** Let `i : Z ⟶ X` be a regular closed immersion of
pure codimension `c`, with `X` smooth of relative dimension `n` over a perfect field `k` and
`Z` regular — hence, by `AlgebraicGeometry.IsRegularImmersion.smooth_comp`, smooth of relative
dimension `m` where `m + c = n`. There is a canonical isomorphism

`Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`,

the inverse of `cl_i(-c)[-2c]`, where `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`, is
`AlgebraicGeometry.Etale.fundamentalClassMap` (an isomorphism by
`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`); it is compatible with étale base change
and with exterior products (`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass`,
`AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject`).

Smooth purity computes `ω_{a_X}` and `ω_{a_Z}`, and the co-projection formula lets one divide
the former into the latter. The relative dimension of `a_Z` is carried as `m` with
`hm : m + c = n` rather than as `n - c`: truncated subtraction would silently read `0` when
`c > n`. -/
theorem nonempty_iso_dualizingComplex_of_isRegularImmersion [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] [PerfectField k] (c n m : ℕ) (hm : m + c = n) (i : Z ⟶ X)
    [IsRegularImmersion c i] [HasCompactification i] (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [QuasiCompact aX] [SmoothOfRelativeDimension n aX] [HasCompactification aX]
    [SmoothOfRelativeDimension m (i ≫ aX)] [HasCompactification (i ≫ aX)]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z] :
    Nonempty (dualizingComplex Λ i ≅
      (twistShift Λ Z (-c : ℤ)).obj (constantComplex Λ Z)) := by
  -- Step 1: `ω_Z ≅ Ri^! ω_X`, `ω_X ≅ Λ_X(n)[2n]` and `ω_Z ≅ Λ_Z(m)[2m]`.
  obtain ⟨eComp⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ i aX
  obtain ⟨θX⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := n) aX (𝟙 (Spec (.of k)))
  obtain ⟨θZ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := m) (i ≫ aX) (𝟙 (Spec (.of k)))
  -- Step 2: the co-projection with `K = Λ_X(0)` and the invertible `L = Λ_X(n)[2n]`.
  obtain ⟨cop⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible Λ i
    (tateObject Λ X 0) ((tateObject Λ X n)⟦2 * (n : ℤ)⟧)
    (boundedConstructibleFiniteTor_tateObject Λ X 0)
    ((boundedConstructibleFiniteTor_tateObject Λ X n).shift _)
    ((isInvertible_tateObject Λ X n).shift _)
  let T : ℤ → _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun a ↦ (tateObject Λ Z a)⟦2 * a⟧
  let R := (R(i)^![Λ]).obj (constantComplex Λ X)
  let tens := derivedTensor (ModuleCat.{u + 1} Λ) Z
  -- `Ri^! Λ_X ⊗ Λ_Z(n)[2n] ≅ Λ_Z(m)[2m]`
  let E : (tens.obj R).obj (T n) ≅ T m :=
    ((tens.mapIso ((R(i)^![Λ]).mapIso
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).symm)).app _ ≪≫
      (tens.obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ i n).symm ≪≫ cop.symm ≪≫
      (R(i)^![Λ]).mapIso
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
          (HasTateTwist.twistObjectZeroIso (Λ := Λ) X)).app _ ≪≫
          derivedTensorLeftUnitor _ X _ ≪≫ (twistShiftConstantComplexIso Λ X n).symm ≪≫
          θX.symm) ≪≫
      (eComp.app _).symm ≪≫ θZ ≪≫ twistShiftConstantComplexIso Λ Z m)
  -- cancel the invertible `Λ_Z(n)[2n]`
  have hmn : (m : ℤ) + -(n : ℤ) = -(c : ℤ) := by lia
  have h0 : (n : ℤ) + -(n : ℤ) = 0 := by lia
  exact ⟨(derivedTensorRightUnitor _ Z R).symm ≪≫
    (tens.obj R).mapIso ((HasTateTwist.twistObjectZeroIso (Λ := Λ) Z).symm ≪≫
      (shiftFunctorZero' _ (2 * ((n : ℤ) + -(n : ℤ))) (by lia)).symm.app _ ≪≫
      eqToIso (by rw [h0]; rfl) ≪≫ (shiftTateObjectAddIso Λ Z n (-(n : ℤ))).symm) ≪≫
    (derivedTensorAssociator _ Z _ _ _).symm ≪≫ (tens.mapIso E).app _ ≪≫
    shiftTateObjectAddIso Λ Z m (-(n : ℤ)) ≪≫ eqToIso (by rw [hmn]) ≪≫
    (twistShiftConstantComplexIso Λ Z _).symm⟩

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The twisted form of purity, `Ri^! (Λ_X(c)[2c]) ≅ Λ_Z`: the co-projection formula moves the
invertible twist out of `Ri^!`, and `Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`). -/
theorem nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] [PerfectField k] (c n m : ℕ) (hm : m + c = n) (i : Z ⟶ X)
    [IsRegularImmersion c i] [HasCompactification i] (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [QuasiCompact aX] [SmoothOfRelativeDimension n aX] [HasCompactification aX]
    [SmoothOfRelativeDimension m (i ≫ aX)] [HasCompactification (i ≫ aX)]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z] :
    Nonempty ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≅
      constantComplex Λ Z) := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_of_isRegularImmersion Λ c n m hm i aX
  obtain ⟨cop⟩ := nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible Λ i
    (tateObject Λ X 0) ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)
    (boundedConstructibleFiniteTor_tateObject Λ X 0)
    ((boundedConstructibleFiniteTor_tateObject Λ X c).shift _)
    ((isInvertible_tateObject Λ X c).shift _)
  let tens := derivedTensor (ModuleCat.{u + 1} Λ) Z
  have h0 : -(c : ℤ) + (c : ℤ) = 0 := by lia
  exact ⟨(R(i)^![Λ]).mapIso
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
          (HasTateTwist.twistObjectZeroIso (Λ := Λ) X)).app _ ≪≫
        derivedTensorLeftUnitor _ X _).symm) ≪≫ cop ≪≫
    (tens.mapIso ((R(i)^![Λ]).mapIso
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) X) ≪≫ θ ≪≫
          twistShiftConstantComplexIso Λ Z _)).app _ ≪≫
    (tens.obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ i c) ≪≫
    shiftTateObjectAddIso Λ Z (-(c : ℤ)) c ≪≫ eqToIso (by rw [h0]; rfl) ≪≫
    (shiftFunctorZero' _ (2 * (0 : ℤ)) (by lia)).app _ ≪≫
    HasTateTwist.twistObjectZeroIso (Λ := Λ) Z⟩

end Purity

section FundamentalClass

variable [Finite Λ] {c : ℕ} {i : Z ⟶ X}

attribute [local instance] HasInvertibleExponent.opens

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ X]
  {k : Type u} [Field k] [PerfectField k] (c) (i) [IsRegularImmersion c i]

end FundamentalClass

end Etale

end AlgebraicGeometry
