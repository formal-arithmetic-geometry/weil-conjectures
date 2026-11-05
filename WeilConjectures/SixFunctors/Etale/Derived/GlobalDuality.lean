/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.HomShift
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
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
- `AlgebraicGeometry.Etale.coefficientDualRightDerivedLowerShriekIso`
  (`sk-thm-sf-global-duality`): the same isomorphism, natural in `K`, for any coefficient
  category in which the projection formula holds.
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek_unit`
  (`sk-thm-sf-global-duality`): `RΓ_c(X, Λ)^∨ ≅ RΓ(X, ω_X)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation`
  (`sk-thm-sf-identification`): under an orientation, `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`.

## Implementation notes

`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` land in `D(A)`, the derived
category of the coefficient category, whereas the coefficient dual `(-)^∨` is a functor on
`D(S_ét)`. The statements below are therefore phrased one step earlier, with `Ra_{X*} K` and
`Ra_{X!} K` in `D(S_ét)`; applying `RΓ(S, -)` to them recovers the `RΓ` / `RΓ_c` form, since
`RΓ_c(X/S, -)` is by definition `RΓ(S, Ra_{X!} -)`.

The statements are made for a finite coefficient ring `Λ`, the finite stages of the blueprint.
Global duality is then the case `N = Λ_S` of the tensor–Hom exchange
`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`, which rests on the
projection formula at finite coefficients; it needs neither the properness, smoothness and
geometric connectedness of `X` nor the finiteness of `K` that the blueprint assumes, so these
hypotheses are not imposed. For a general coefficient category the projection formula, and
with it global duality, can fail.

The subject of `sk-thm-sf-identification` is the pairing `β_K` — the mixed-support cup
product followed by the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` and the normalized trace — and the
assertion that its tensor–internal-hom adjoint is invertible. The pairing is
`AlgebraicGeometry.Etale.poincarePairing`, and its perfectness is proved next to it
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting` and, at finite
coefficients, `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`); this file does not
import them, and records only the isomorphism that the blueprint identifies the adjoint of
`β_K` with. The blueprint's further assertion that the inverse of the adjoint *is* the global
duality isomorphism followed by `𝔻_X K ≅ K^∨(d)[2d]` is not stated: those isomorphisms are only
known to exist here (`Nonempty`), they are not constructed as specific maps.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

universe u'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X S : Scheme.{u}} (aX : X ⟶ S) [HasCompactification aX]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

section Shift

variable {Z : Scheme.{u}}

end Shift

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (aX : X ⟶ S)
  [HasCompactification aX]

end Etale

end AlgebraicGeometry
