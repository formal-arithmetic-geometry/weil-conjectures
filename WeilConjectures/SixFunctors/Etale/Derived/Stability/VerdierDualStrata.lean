/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualLocal
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation

/-!
# The Tor bound of the Verdier dual, by noetherian induction

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and
`Λ` a finite ring whose exponent is invertible in `k`. If `K ∈ Dᵇc(X, Λ)` has Tor amplitude in
`[a, b]`, then `𝔻_X K = RHom(K, ω_X)` is bounded constructible with Tor amplitude in
`[-b - 2d, -a]`
(`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed`,
`lem-weil-verdier-preservation-strata`).

The proof is a noetherian induction on the support, along the localization triangles of the
*dualizing complex* `Ri_! Ri^! ω ⟶ ω ⟶ Rj_* j^* ω ⟶` for a closed immersion `i` with open
complement `j`, to which the triangulated functor `RHom(K, -)` is applied:

- `RHom(K, Ri_! Ri^! ω_Y) ≅ Ri_! 𝔻_Z(i^* K)`, handled by induction;
- `RHom(K, Rj_* j^* ω_Y) ≅ Rj_* 𝔻_U(j^* K)`; on a dense open `U` of the reduction of the support
  which is smooth of pure relative dimension `n ≤ d`, irreducible, and on which a flat model of
  `K` is lisse, `𝔻_U(j^* K)` is bounded constructible with Tor amplitude `[-b - 2n, -a - 2n]`
  (`AlgebraicGeometry.Etale.exists_boundedConstructible_and_torAmplitudeIn_verdierDual`), and the
  direct image `Rj_*` moves this to `[-b - 2n, -a]`
  (`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`,
  `thm-sf-direct-image-tor-amplitude`).

Working with the localization triangles of `ω` rather than of `K` only uses the exactness of
the internal hom in its *second* variable.
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

/-! ### Generalities -/

/-! ### The two pieces of the localization triangle of the dualizing complex -/

/-! ### The localization step -/

/-! ### A lisse smooth open -/

end Etale

end AlgebraicGeometry
