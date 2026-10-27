/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Finite-stage étale Verdier biduality over a general base field

`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed` proves Verdier biduality
on `Dctf(X, Λ)` for `X` separated of finite type over an algebraically closed field. This file
extends it to other base fields `k` (blueprint `det-pd-biduality-coefficients`, (i)): biduality is
local on `X`, and for `X` affine, closed in `𝔸ⁿ_k`, the pullback `g : X_{k̄} ⟶ X` to an algebraic
closure carries `δ_K` to `δ_{g^* K}` (the geometric generic fibre comparison
`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_generic`
for `Spec k̄ ⟶ Spec k`), and is conservative, every geometric point of `X` factoring through
`X_{k̄}`.

## Main results

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_perfectField`: biduality over a
  perfect field.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Finite-stage étale Verdier biduality over a perfect field** (blueprint
`det-pd-biduality-coefficients`, (i)): for a finite ring `Λ` whose exponent is invertible on the
perfect field `k` and `X` separated, quasi-compact and locally of finite type over `k`, the
double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every `K ∈ Dctf(X, Λ)`. -/
theorem isIso_verdierDualDoubleDual_app_of_perfectField {k : Type u} [Field k] [PerfectField k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) :=
  sorry

/-- **Finite-stage étale Verdier biduality over an arbitrary field** (blueprint
`det-pd-biduality-coefficients`, (i)): for a finite ring `Λ` whose exponent is invertible on the
field `k` and `X` separated, quasi-compact and locally of finite type over `k`, the double-dual
morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every `K ∈ Dctf(X, Λ)`. -/
theorem isIso_verdierDualDoubleDual_app_of_field {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ aX).app K) :=
  sorry

end AlgebraicGeometry.Etale
