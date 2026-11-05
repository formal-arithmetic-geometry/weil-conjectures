/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualStrata

/-!
# Verdier duality preserves `Dctf`, with the Tor bound

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and
`Λ` a finite ring whose exponent is invertible in `k`. If `K ∈ Dᵇc(X, Λ)` has Tor amplitude in
`[a, b]`, then `𝔻_X K = RHom(K, ω_X)` is bounded constructible with Tor amplitude in
`[-b - 2d, -a]`
(`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed`,
`lem-weil-verdier-preservation-strata`).

The proof is a noetherian induction on the closed subsets `T ⊆ X`, for all closed subschemes
`Z ⊆ X` supported in `T`: a reduced `Z` is cut into a dense open `U`, smooth over `k`, on which
`K` is lisse and where the Verdier dual is computed by
`AlgebraicGeometry.Etale.exists_boundedConstructible_and_torAmplitudeIn_verdierDual`, and its
closed complement, handled by induction; the localization step is
`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_verdierDual_of_localization`.
A non-reduced `Z` is reduced to `Z_red` by the same step, with empty open complement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Etale

end AlgebraicGeometry
