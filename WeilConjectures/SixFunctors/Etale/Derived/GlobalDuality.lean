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
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalVerdierDuality
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

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (aX : X ⟶ S)
  [HasCompactification aX]

/-- Blueprint `sk-thm-sf-global-duality`: Global Verdier duality. This is also blueprint
`thm-pod-global-verdier-duality` (Global Verdier duality at the point); the canonical form of the
isomorphism is `AlgebraicGeometry.Etale.globalVerdierDualityIso`.

For `a_X : X ⟶ S` admitting a compactification, a finite coefficient ring `Λ` and `K` an
object of `D(X_ét, Λ)`, the coefficient dual of the compactly supported cohomology of `K` is the
cohomology of the Verdier dual of `K`:

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`.

It is stated here for `Ra_{X!} K` and `Ra_{X*} (𝔻_X K)` in `D(S_ét)`; applying `RΓ(S, -)`
gives the displayed form, since `RΓ_c(X/S, -) = RΓ(S, Ra_{X!} -)`. It is the tensor–Hom
exchange `Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)` at `N = Λ_S`. -/
theorem nonempty_iso_coefficientDual_rightDerivedLowerShriek
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K))) :=
  (nonempty_iso_derivedHom_rightDerivedLowerShriek Λ aX K (𝟙_ _)).map Iso.symm

/-- Blueprint `sk-thm-sf-identification`: The derived Poincaré pairing is the duality
isomorphism.

With an orientation `o` of `a_X` of relative dimension `d` and with `K` perfect over `Λ_X`,
there is an isomorphism

`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`,

again written one step earlier, with `Ra_{X*}` and `Ra_{X!}` in `D(S_ét)`. The blueprint
identifies this isomorphism with the tensor–internal-hom adjoint of the derived Poincaré
pairing `β_K`, and concludes that `β_K` is perfect; that perfectness is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`. -/
theorem nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation [HasTateTwist Λ]
    {d : ℕ} (o : Orientation Λ aX d)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKperf : IsDualizable K) :
    Nonempty (((R((aX)_*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).obj
            (tateObject Λ X d)))⟦(2 * d : ℤ)⟧ ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K))) := by
  obtain ⟨e₁⟩ := nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ aX K
  obtain ⟨e₂⟩ := Orientation.nonempty_iso_verdierDual_coefficientDual o hKperf
  exact ⟨((R((aX)_*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).symm.app _ ≪≫
    (R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).commShiftIso
        (2 * d : ℤ)).symm.app (tateObject Λ X d) ≪≫ e₂.symm) ≪≫ e₁.symm⟩

end Etale

end AlgebraicGeometry
