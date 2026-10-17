/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Dual

/-!
# Poincaré duality for a lisse Weil sheaf

Let `k₀ = 𝔽_q` be a finite field, `ℓ ≠ p` a prime, `X₀` a smooth, separated `k₀`-scheme of finite
type and pure dimension `d`, and `F` a lisse Weil sheaf on `X₀` with dual `F^∨`. Poincaré
duality pairs `H_c^i(X₀ ⊗ k̄, F)` perfectly with `H^{2d-i}(X₀ ⊗ k̄, F^∨)`, with values in the line
`ℚ̄_ℓ(-d)` on which the geometric Frobenius acts by `q^d`. The degreewise perfectness of another
section of the blueprint is stated here, with `sorry`, in this form.

A perfect pairing `M × N ⟶ K` of Frobenius modules with `⟨F x, F y⟩ = c ⟨x, y⟩` identifies `M`
with the dual `N^∨` with Frobenius rescaled by `c`
(`FrobeniusModule.Equiv.ofIsPerfPair`); in particular, `H_c^i(F) ≅ H^{2d-i}(F^∨)^∨(-d)`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
  (`thm-pod-degreewise-perfectness-over-a-field` for lisse `K`, with
  `thm-pod-equivariance-of-the-twisted-pairing`): the perfect Frobenius-equivariant pairings.
- `FrobeniusModule.Equiv.dual`: the dual of an isomorphism of Frobenius modules.
- `FrobeniusModule.Equiv.ofIsPerfPair`: a perfect pairing multiplying the Frobenius by `c`
  identifies `M` with `N^∨` rescaled by `c`.

## Implementation notes

As in `WeilConjectures.WeilSheaf.TraceIsomorphism`, Weil complexes have no `Ra^!`, orientation or
derived tensor product yet, so the duality is stated existentially: there are perfect pairings
on which the Frobenius acts as asserted.
-/

@[expose] public section

universe u v

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The dual `e^∨ : M^∨ ≅ N^∨`, `f ↦ f ∘ e⁻¹`, of an isomorphism of Frobenius modules
`e : M ≅ N`. -/
@[simps toLinearEquiv]
noncomputable def Equiv.dual {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    M.dual.Equiv N.dual where
  toLinearEquiv := e.toLinearEquiv.symm.dualMap
  map_frobenius f := by
    refine LinearMap.ext fun y ↦ ?_
    have h := e.symm.map_frobenius (N.frobenius.symm y)
    rw [LinearEquiv.apply_symm_apply, Equiv.symm_toLinearEquiv] at h
    erw [LinearEquiv.dualMap_apply]
    rw [dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
      LinearEquiv.symm_apply_apply]
    rfl

/-- A perfect pairing `P : M × N ⟶ K` of Frobenius modules with `P (F x) (F y) = c * P x y`,
`c ≠ 0`, identifies `M` with the dual `N^∨` with Frobenius rescaled by `c`: the value line is
`K` with Frobenius acting by `c`. -/
noncomputable def Equiv.ofIsPerfPair {M : FrobeniusModule.{max u v, v} K}
    {N : FrobeniusModule.{u, v} K} (P : M.carrier →ₗ[K] N.carrier →ₗ[K] K) [P.IsPerfPair]
    {c : K} (hc : c ≠ 0) (hP : ∀ x y, P (M.frobenius x) (N.frobenius y) = c * P x y) :
    M.Equiv (N.dual.rescale c) where
  toLinearEquiv := P.toPerfPair
  map_frobenius x := by
    refine (LinearMap.ext fun y ↦ ?_ : P.toPerfPair (M.frobenius x) =
      c • N.dual.frobenius (P.toPerfPair x)).trans (frobeniusEnd_rescale_apply hc _).symm
    rw [LinearMap.smul_apply, dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply, smul_eq_mul, ← hP,
      LinearEquiv.apply_symm_apply]

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-pod-degreewise-perfectness-over-a-field` (for `K = F` a lisse Weil sheaf, so
that `K^∨ = F^∨`, in its line-valued form `H_c^i(X, K) × H^{2d-i}(X, K^∨) ⟶ ℚ̄_ℓ(-d)`), with the
Frobenius equivariance of `thm-pod-equivariance-of-the-twisted-pairing`: for `X₀` smooth,
separated, of finite type and pure dimension `d` over `k₀` and `F` lisse, the degreewise
Poincaré pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect, and
`⟨F x, F y⟩ = q^d ⟨x, y⟩` for the geometric Frobenius `F` (Frobenius acts on `ℚ̄_ℓ(-d)` by
`q^d`). Properness is not needed.

For `F = ℚ̄_ℓ` this is equivalent to
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_adicConstant`, the
Frobenius of `H^j(ℚ̄_ℓ(d))` being `q^{-d}` times that of `H^j(ℚ̄_ℓ)`. -/
theorem exists_isPerfPair_compactlySupportedCohomology_dual (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    ∃ P : (F.compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
        ((F.dual hF).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P ((F.compactlySupportedCohomology i).frobenius x)
        (((F.dual hF).cohomology j).frobenius y) = (Nat.card k₀ : PadicAlgCl l) ^ d * P x y :=
  sorry

end AlgebraicGeometry.WeilSheaf
