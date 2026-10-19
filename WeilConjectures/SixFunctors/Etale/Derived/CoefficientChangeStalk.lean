/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-!
# Geometric stalks commute with finite-level coefficient reduction

Let `ρ : Λ →+* Λ'` be a surjection of finite coefficient rings whose exponent is invertible on a
separably closed field `k`, and `x̄ : Spec k ⟶ X` a geometric point. The canonical coefficient
comparison `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄`
(`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)` (blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
  {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (x : Spec (.of k) ⟶ X)


/-- Blueprint `thm-trf-finite-coefficient-map` (subsection `sk-p-trace-coeff`), the pullback
isomorphism at a geometric point: for a surjection `ρ : Λ →+* Λ'` of finite rings whose exponent
is invertible on `k`, the canonical coefficient comparison
`K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` of geometric stalks
(`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)`. -/
theorem isCoefficientChange_geometricStalkRestrictScalarsIso [Finite Λ] [Finite Λ']
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ) :
    IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x)
      (geometricStalkRestrictScalarsIso ρ x) :=
  sorry

end AlgebraicGeometry.Etale
