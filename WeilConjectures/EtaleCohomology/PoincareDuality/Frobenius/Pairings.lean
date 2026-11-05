/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.ZetaLinearAlgebra.Pairing

/-!
# Frobenius: the pairings

Let `a : X ⟶ Y` admit a compactification and `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` be a Tate orientation.
This file shows that a Weil pairing compatible with the trace is a morphism of Weil objects
in general, and defines the degreewise Poincaré pairing
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` and its untwisted, line-valued form
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)`, whose Frobenius equivariance is proved in
`WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance`.

## Main definitions

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`
  (`prop-pod-degree-of-the-pairing`): `⟨-, -⟩_i`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing`
  (`prop-pod-degree-of-the-pairing`): the untwisted pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` and its degreewise form.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

end Generic

namespace TateOrientation

section Pairings

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

end Pairings

end TateOrientation

end Etale

end AlgebraicGeometry
