/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# The Verdier dual on `Dctf`: Tor bound and boundary exchange

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k` and schemes
separated of finite type over `k`, this file states

- `AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual` (`lem-weil-verdier-preservation-strata`):
  the Verdier dual `𝔻_X` sends Tor amplitude `[a, b]` to `[-b - 2d, -a]` when `dim X ≤ d`;
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`
  (`cor-weil-boundary-duality-discharge`): for a closed immersion `i : Z ⟶ T` the boundary
  exchange `i^* 𝔻_T L ≅ 𝔻_Z Ri^! L` holds on `Dctf(T)`.

The canonical exchange map of the blueprint is not constructed; the exchange is stated as the
existence of an isomorphism, as in `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `lem-weil-verdier-preservation-strata`: Verdier duality preserves `Dctf`.

Let `X` be separated of finite type over `k`, `ω_X = Ra_X^! Λ` and `𝔻_X = RHom(-, ω_X)`. Then
`𝔻_X` carries `Dctf(X, Λ)` into itself, and more precisely, if `dim X ≤ d` and `K ∈ Dctf(X, Λ)`
has Tor amplitude in `[a, b]`, then `𝔻_X K` has Tor amplitude in `[-b - 2d, -a]`. The bound is
independent of the exponent of `Λ`. The first half is
`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem torAmplitudeIn_verdierDual {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
      ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) :=
  sorry

/-- Blueprint `cor-weil-boundary-duality-discharge`: Discharge of the boundary duality input.

Let `k` be algebraically closed, and let `i : Z ⟶ T` be a closed immersion of schemes
separated of finite type over `k` (for instance two locally closed pieces of a separated
finite-type `Y`). For every `L ∈ Dctf(T, Λ)` the boundary exchange
`β_L : i^* 𝔻_T L ⟶ 𝔻_Z Ri^! L` is an isomorphism; here it is stated as the existence of an
isomorphism. That `𝔻_T` preserves `Dctf(T, Λ)`, the first clause of the boundary duality input,
is `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem nonempty_iso_leftDerivedUpperStar_verdierDual [IsAlgClosed k] {Z T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasCompactification aT] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [HasCompactification (i ≫ aT)]
    {L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T L) :
    Nonempty ((L((i)^*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj (op L)) ≅
      (verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aT)).obj
        (op ((R(i)^![ModuleCat.{u + 1} Λ]).obj L))) :=
  sorry

end Etale

end AlgebraicGeometry
