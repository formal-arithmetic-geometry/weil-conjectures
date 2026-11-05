/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation

/-!
# General Verdier biduality at a finite stage

For `X` separated of finite type over a field `k` and a finite coefficient ring `Λ` whose
exponent is invertible on `k`, the Verdier dual `𝔻_X = RHom(-, ω_X)` carries `Dctf(X, Λ)` into
itself, with the Tor interval `[a, b]` going to `[-b - 2d, -a]` when `dim X ≤ d`
(`lem-weil-verdier-preservation-strata`), and, for `k` algebraically closed, the double-dual map
`δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism, so that `𝔻_X` is an anti-equivalence of `Dctf(X, Λ)`
(`sk-prop-sf-biduality-general`, `thm-fix-general-biduality`,
`thm-weil-etale-geometric-biduality`).

## Implementation notes

The blueprint works over `k = 𝔽̄_q`. Its proof of preservation uses a stratification by smooth
strata, available over a perfect field, and its proof of biduality is an induction over
algebraically closed fields through geometric generic fibres. The statements below therefore
assume `k` perfect, respectively algebraically closed. The proofs are
`AlgebraicGeometry.Etale.constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField`
and `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

end Etale

end AlgebraicGeometry
