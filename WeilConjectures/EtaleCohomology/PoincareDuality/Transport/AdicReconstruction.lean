/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# The derived Poincaré pairing at the integral stage and its reductions

Let `k` be separably closed, `Λ` a commutative ring (the integral stage `Λ = 𝒪_E`), `ϖ ∈ Λ` a
nonzerodivisor (a uniformizer `ϖ_E`), `a : X ⟶ Spec k` admitting a compactification with
`Ra^!`, and `γ : V[2d] ≅ Ra^! Λ` a purity isomorphism. For `K ∈ D(X_ét, Λ)` perfect over `Λ_X`
the derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ_Λ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is perfect, and so are the pairings `β_{K_n}` of its reductions `K_n = K ⊗ᴸ (Λ/ϖⁿ)_X`, the
finite levels `A_{E,n} = 𝒪_E/ϖⁿ` of blueprint `thm-pod-adic-reconstruction-and-scalar-extension`
(as elsewhere in the repository, an object at the level `A_{E,n}` is recorded in `D(X_ét, 𝒪_E)`
through its restriction of scalars).

## Main statements

- `AlgebraicGeometry.Etale.isDualizable_reductionModIdeal`: `K_n` is perfect over `Λ_X` if `K` is.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_integral`
  (`thm-pod-adic-reconstruction-and-scalar-extension`, integral part): `β_K` and all the `β_{K_n}`
  are perfect.

## Not formalised

The blueprint obtains the `𝒪_E` pairing as the realization of the system of the finite-level
pairings under the uniform-tower reconstruction; in the repository the integral derived
Poincaré duality is proved directly at `Λ = 𝒪_E`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable`), so
no reconstruction is needed. The second half of the node, the transport of the pairing, its
adjoint, the degreewise maps and the Frobenius squares along localization `𝒪_E ⟶ E` and finite
extension `E ⟶ L`, is not stated: the rational stage
`AlgebraicGeometry.DerivedCategoryDerivedCompleteRational` has no `Rf_!`, `Rf_*`, `⊗ᴸ` or
`RHom`, and the derived base change `AlgebraicGeometry.Etale.derivedBaseChange` along
`𝒪_E ⟶ 𝒪_L` (`WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension`) is not known to be
monoidal or to commute with `Ra_!`, `Ra_*` and the trace.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The reduction `K ⊗ᴸ (Λ/ϖⁿ)_X` of a dualizable (that is, perfect over `Λ_X`) object `K` of
`D(X_ét, Λ)` is dualizable, for `ϖ` a nonzerodivisor of `Λ`: `(Λ/ϖⁿ)_X` is dualizable
(`AlgebraicGeometry.Etale.isDualizable_constantSingle_quotient_span_pow`). -/
theorem isDualizable_reductionModIdeal {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    IsDualizable ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) :=
  hK.tensorObj (isDualizable_constantSingle_quotient_span_pow hϖ n X)

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [HasCompactification a] [(R(a)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {d : ℕ}

/-- Blueprint `thm-pod-adic-reconstruction-and-scalar-extension`: Adic reconstruction and scalar
extension (integral part).

Let `k` be separably closed, `Λ = 𝒪_E` (any commutative ring), `ϖ` a nonzerodivisor of `Λ`,
`a : X ⟶ Spec k` admitting a compactification with a right adjoint `Ra^!` of `Ra_!`, and
`γ : V[2d] ≅ Ra^! Λ` a purity isomorphism (`V = Λ_X(d)`). For `K` perfect over `Λ_X`, the
`𝒪_E`-valued derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ_{𝒪_E} RΓ(X, K^∨(d))[2d] ⟶ 𝒪_E`

is perfect: the inverse of its adjoint is an isomorphism
`RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]` over `𝒪_E`. So are the pairings `β_{K_n}` of the finite
levels `K_n = K ⊗ᴸ (𝒪_E/ϖⁿ)_X`. -/
theorem isPerfectPairing_poincarePairing_integral
    {V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : V⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) :
    IsPerfectPairing (poincarePairing a γ K) ∧
      ∀ n : ℕ, IsPerfectPairing
        (poincarePairing a γ ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K)) :=
  ⟨isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a γ hK, fun n ↦
    isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a γ
      (isDualizable_reductionModIdeal hϖ n hK)⟩

end Etale

end AlgebraicGeometry
