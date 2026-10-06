/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Global Verdier duality and the derived Poincaré pairing

Let `X` be smooth, proper and geometrically connected of pure relative dimension `d` over a
base `S`, with structure morphism `a_X : X ⟶ S`. Global Verdier duality is the case `Y = S`
of the Verdier-duality exchange `sk-thm-sf-verdier-exchange`: the coefficient dual of the
compactly supported cohomology of `K` is the ordinary cohomology of the Verdier dual of `K`,

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

Under an orientation `ω_X ≅ Λ(d)[2d]` the Verdier dual of a perfect `K` is `K^∨(d)[2d]`, and
global duality becomes the statement that the derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is perfect: its tensor–internal-hom adjoint is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`
  (`sk-thm-sf-global-duality`): `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation`
  (`sk-thm-sf-identification`): under an orientation, `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`.

## Implementation notes

`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` land in `D(A)`, the derived
category of the coefficient category, whereas the coefficient dual `(-)^∨` is a functor on
`D(S_ét)`. The statements below are therefore phrased one step earlier, with `Ra_{X*} K` and
`Ra_{X!} K` in `D(S_ét)`; applying `RΓ(S, -)` to them recovers the `RΓ` / `RΓ_c` form, since
`RΓ_c(X/S, -)` is by definition `RΓ(S, Ra_{X!} -)`.

The blueprint assumes *either* that `X` is proper *or* that `X = X₀ ×_{k₀} k` for a smooth
separated geometrically connected finite-type scheme `X₀` over a finite field. The second
alternative needs the model datum `X₀`, which this repository does not yet have, so only the
proper case is stated here. `[IsProper a_X]` also supplies `[HasCompactification a_X]`, hence
separatedness and finite type.

The subject of `sk-thm-sf-identification` is the pairing `β_K` — the mixed-support cup
product followed by the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` and the normalized trace — and the
assertion that its tensor–internal-hom adjoint is invertible. The pairing is
`AlgebraicGeometry.Etale.poincarePairing`, and its perfectness at finite coefficients is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`; this file does not import them,
and records only the isomorphism that the blueprint identifies the adjoint of `β_K` with.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X S : Scheme.{u}} (aX : X ⟶ S) [IsProper aX] (d : ℕ)
  [SmoothOfRelativeDimension d aX] [GeometricallyConnected aX]

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality.

For `X` smooth, proper and geometrically connected of pure relative dimension `d` over `S`,
and `K` an object of `Dctf(X, A)`, the coefficient dual of the compactly supported cohomology
of `K` is the cohomology of the Verdier dual of `K`:

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

It is stated here for `Ra_{X!} K` and `Ra_{X*} (𝔻_X K)` in `D(S_ét)`; applying `RΓ(S, -)`
gives the displayed form, since `RΓ_c(X/S, -) = RΓ(S, Ra_{X!} -)`. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    Nonempty ((DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K)) ≅
      (R((aX)_*[A])).obj ((verdierDual A aX).obj (op K))) :=
  sorry

/-- Blueprint `sk-thm-sf-identification`: The derived Poincaré pairing is the duality
isomorphism.

Under the hypotheses of `sk-thm-sf-global-duality`, with an orientation `o` of `a_X` of
relative dimension `d` and with `K` perfect over `Λ_X`, there is an isomorphism

`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`,

again written one step earlier, with `Ra_{X*}` and `Ra_{X!}` in `D(S_ét)`. The blueprint
identifies this isomorphism with the tensor–internal-hom adjoint of the derived Poincaré
pairing `β_K`, and concludes that `β_K` is perfect; see the module docstring. -/
theorem nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation
    (o : Orientation A aX d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) (hKperf : IsDualizable K) :
    Nonempty (((R((aX)_*[A])).obj
        ((DerivedCategory.coefficientDual A X).obj (op K) ⊗ o.twist))⟦(2 * d : ℤ)⟧ ≅
      (DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K))) :=
  sorry

end Etale

end AlgebraicGeometry
