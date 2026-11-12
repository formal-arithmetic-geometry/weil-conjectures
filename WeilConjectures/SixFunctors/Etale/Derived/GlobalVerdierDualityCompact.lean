/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Global Verdier duality with compact supports on the dual side

Let `k` be an algebraically closed field, `a_X : X ⟶ Spec k` separated of finite type, and `Λ` a
finite coefficient ring whose exponent is invertible on `k`. Global Verdier duality
(`AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`) identifies
`RΓ_c(X, K)^∨` with `RΓ(X, 𝔻_X K)`. This file proves the companion isomorphism (10.6) of
blueprint `theorem-global-verdier-duality`,

`RΓ_c(X, 𝔻_X K) ≅ RHom_Λ(RΓ(X, K), Λ)`

for `K ∈ Dctf(X, Λ)`. Applying the first isomorphism to `𝔻_X K`, which lies in `Dctf(X, Λ)`, and
Verdier biduality `𝔻_X 𝔻_X K ≅ K` give `RΓ_c(X, 𝔻_X K)^∨ ≅ RΓ(X, K)`; since `RΓ_c(X, 𝔻_X K)`
lies in `Dctf` of the point, it is dualizable, hence equal to its double dual.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_verdierDual`: the isomorphism
  `Ra_! 𝔻_X K ≅ (Ra_* K)^∨` in the point category `D(Spec k_ét, Λ)`.
- `AlgebraicGeometry.Etale.nonempty_iso_compactlySupportedGlobalSections_verdierDual`: the
  isomorphism `RΓ_c(X, 𝔻_X K) ≅ RHom_Λ(RΓ(X, K), Λ)` in `D(Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]

/-- Blueprint `theorem-global-verdier-duality--2`, in the point category: for `k`
algebraically closed, `a_X : X ⟶ Spec k` separated of finite type, `Λ` finite with exponent
invertible on `k` and `K ∈ Dctf(X, Λ)`,

`Ra_! 𝔻_X K ≅ (Ra_* K)^∨`

in `D(Spec k_ét, Λ)`. Applying `RΓ(Spec k, -)` gives (10.6); see
`AlgebraicGeometry.Etale.nonempty_iso_compactlySupportedGlobalSections_verdierDual`. -/
theorem nonempty_iso_rightDerivedLowerShriek_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((R(aX)_![ModuleCat.{u + 1} Λ]).obj ((verdierDual Λ aX).obj (op K)) ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        (op ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj K))) := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hD := constructibleFiniteTor_verdierDual Λ aX hK
  have hc : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k))
      ((R(aX)_![ModuleCat.{u + 1} Λ]).obj ((verdierDual Λ aX).obj (op K))) :=
    constructibleFiniteTor_rightDerivedLowerShriek Λ (𝟙 _) aX hD
  let M := (R(aX)_![ModuleCat.{u + 1} Λ]).obj ((verdierDual Λ aX).obj (op K))
  have hM : IsIso ((DerivedCategory.coefficientDualDoubleDual (ModuleCat.{u + 1} Λ)
      (Spec (.of k))).app M) :=
    DerivedCategory.isIso_coefficientDualDoubleDual_app
      (isDualizable_of_constructibleFiniteTor_of_subsingleton Λ hc)
  have := isIso_verdierDualDoubleDual_app Λ aX hK
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ aX
    ((verdierDual Λ aX).obj (op K))
  let j : (R((aX)_*[ModuleCat.{u + 1} Λ])).obj K ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj (op M) :=
    (R((aX)_*[ModuleCat.{u + 1} Λ])).mapIso (asIso ((verdierDualDoubleDual Λ aX).app K)) ≪≫
      e.symm
  exact ⟨asIso ((DerivedCategory.coefficientDualDoubleDual (ModuleCat.{u + 1} Λ)
      (Spec (.of k))).app M) ≪≫
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso j.op⟩

/-- Blueprint `theorem-global-verdier-duality--2`: Global Verdier duality (10.6).

For `k` algebraically closed, `a_X : X ⟶ Spec k` separated of finite type, `Λ` finite with
exponent invertible on `k` and `K ∈ Dctf(X, Λ)`, there is an isomorphism of `Λ`-module complexes

`RΓ_c(X, 𝔻_X K) ≅ RHom_Λ(RΓ(X, K), Λ)`.

It is `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_verdierDual` read through the
evaluation `RΓ(Spec k, -)`, which carries the coefficient dual of the point category to the dual
over `Λ` and `RΓ(Spec k, Ra_* -)` to `RΓ(X, -)`. -/
theorem nonempty_iso_compactlySupportedGlobalSections_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj
        ((verdierDual Λ aX).obj (op K)) ≅
      (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)).obj (𝟙_ _)) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerShriek_verdierDual Λ aX hK
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence
    (ModuleCat.{u + 1} Λ) (Spec (.of k)) ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj K)
  exact ⟨(rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso e₁ ≪≫ e₂ ≪≫
    (MonoidalClosed.internalHom.mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) aX).app
        K).symm.op).app (𝟙_ _)⟩

end Etale

end AlgebraicGeometry
