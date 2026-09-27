/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Global Verdier duality and the derived Poincaré pairing

Let `X` be smooth, separated of finite type and geometrically connected of pure relative
dimension `d` over a base `S`, with structure morphism `a_X : X ⟶ S` admitting a
compactification. Global Verdier duality is the case `Y = S` of the Verdier-duality exchange
`sk-thm-sf-verdier-exchange`: the coefficient dual of the compactly supported cohomology of
`K` is the ordinary cohomology of the Verdier dual of `K`,

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

Under an orientation `ω_X ≅ Λ(d)[2d]` the Verdier dual of a perfect `K` is `K^∨(d)[2d]`, and
global duality becomes the statement that the derived Poincaré pairing

`RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is perfect: its tensor–internal-hom adjoint is an isomorphism.

## Implementation notes

`AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` land in `D(A)`, the derived
category of the coefficient category, whereas the coefficient dual `(-)^∨` is a functor on
`D(S_ét)`. The statements below are therefore phrased one step earlier, with `Ra_{X*} K` and
`Ra_{X!} K` in `D(S_ét)`; applying `RΓ(S, -)` to them recovers the `RΓ` / `RΓ_c` form, since
`RΓ_c(X/S, -)` is by definition `RΓ(S, Ra_{X!} -)`.

The hypothesis "smooth of pure dimension `d`" is spelled `SmoothOfRelativeDimension d a_X`,
which implies `Smooth a_X`; "of finite type" is the pair `LocallyOfFiniteType a_X` and
`QuasiCompact a_X`. The Tate twist `Λ(d)` is taken as a parameter `T`, an invertible object
of `D(X_ét)`, and the orientation as a supplied isomorphism `ω_X ≅ T⟦2d⟧`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`
  (`sk-thm-sf-global-duality`): `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.
- `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_of_orientation`
  (`sk-thm-sf-identification`): the derived Poincaré pairing is the duality isomorphism.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

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

variable {X S : Scheme.{u}}

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality.

Let `X` be smooth, separated of finite type and geometrically connected of pure relative
dimension `d` over the base `S`, with structure morphism `a_X : X ⟶ S` admitting a
compactification, and let `K` be an object of `Dctf(X, A)`. Then the coefficient dual of the
compactly supported cohomology of `K` is the cohomology of the Verdier dual of `K`:

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`,

naturally in `K` and compatibly with finite reduction, scalar extension and shifts. For
`K = Λ_X` it reads `RΓ_c(X, Λ)^∨ ≅ RΓ(X, ω_X)`.

This is the Verdier-duality exchange `sk-thm-sf-verdier-exchange` applied to `f = a_X` over
`Y = S`, where `𝔻_S` is the coefficient dual because `ω_S ≅ Λ_S`. It is stated here for
`Ra_{X!} K` and `Ra_{X*} (𝔻_X K)` in `D(S_ét)`; applying `RΓ(S, -)` gives the displayed form,
since `RΓ_c(X/S, -) = RΓ(S, Ra_{X!} -)`. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek (aX : X ⟶ S)
    [HasCompactification aX] (d : ℕ) [SmoothOfRelativeDimension d aX] [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [GeometricallyConnected aX] [ConnectedSpace X]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.boundedConstructible A X K ∧ DerivedCategory.finiteTorAmplitude A X K) :
    Nonempty ((DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K)) ≅
      (R((aX)_*[A])).obj ((verdierDual A aX).obj (op K))) :=
  sorry

/-- Blueprint `sk-thm-sf-identification`: The derived Poincaré pairing is the duality
isomorphism.

Under the hypotheses of `sk-thm-sf-global-duality`, with an orientation fixed — an invertible
`T` in `D(X_ét)`, standing for the Tate twist `Λ(d)`, together with an isomorphism
`ω_X ≅ T⟦2d⟧` — and with `K` site-perfect over `Λ_X`, the tensor–internal-hom adjoint of the
derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is the canonical isomorphism `RΓ(X, K^∨(d))[2d] ≅ RHom(RΓ_c(X, K), Λ)`, whose inverse is the
global duality isomorphism followed by `𝔻_X K ≅ K^∨(d)[2d]`. In particular `β_K` is a perfect
pairing. The pairing itself is the mixed-support cup product followed by the evaluation
`K ⊗ᴸ K^∨ ⟶ Λ_X` and the normalized trace, the counit of `Ra_{X!} ⊣ Ra_X^!` read through the
orientation; only the resulting isomorphism is recorded here.

The classical form of this statement is the family of degreewise pairings

`⟨-,-⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ`,

perfect for `X` proper and `Λ` one of the coefficient stages `A_{E,n}`, `E` or `ℚ̄_ℓ`, over
`A_{E,n}` because that ring is self-injective, so that `Hom(-, Λ)` is exact. At the integral
stage `Λ = 𝒪_E` the degreewise form fails in general: a torsion class in `H^i_c` pairs to
zero with everything, and `H^{-i}(RΓ_c^∨)` acquires an `Ext¹` term from the torsion of
`H^{i+1}_c`. Only the derived statement below holds at that stage.

As in `nonempty_iso_coefficientDual_rightDerivedLowerShriek`, `RΓ` and `RΓ_c` are written as
`Ra_{X*}` and `Ra_{X!}` in `D(S_ét)`. -/
theorem nonempty_iso_coefficientDual_of_orientation (aX : X ⟶ S)
    [HasCompactification aX] (d : ℕ) [SmoothOfRelativeDimension d aX] [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [GeometricallyConnected aX] [ConnectedSpace X]
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hT : DerivedCategory.invertible A X T)
    (hor : Nonempty (dualizingComplex A aX ≅ T⟦(2 * d : ℤ)⟧))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.boundedConstructible A X K ∧ DerivedCategory.finiteTorAmplitude A X K)
    (hKperf : DerivedCategory.sitePerfect A X K) :
    Nonempty (((R((aX)_*[A])).obj ((DerivedCategory.coefficientDual A X).obj (op K) ⊗ T))⟦
        (2 * d : ℤ)⟧ ≅
      (DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K))) :=
  sorry

end Etale

end AlgebraicGeometry
