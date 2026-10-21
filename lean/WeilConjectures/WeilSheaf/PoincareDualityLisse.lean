/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Degreewise Poincaré duality for lisse Weil sheaves

Let `X₀` be a smooth separated `k₀`-scheme of finite type and pure dimension `d` and `F` a lisse
Weil sheaf on `X₀`, with coefficient dual `F^∨` and Tate twist `F^∨(d)`, the constant twist of
`F^∨` by `χ_ℓ(σ)ᵈ = q⁻ᵈ`. Poincaré duality with coefficients `F` says that the degreewise
pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
  (`thm-pod-degreewise-perfectness-over-a-field`, with the Frobenius invariance of
  `thm-pod-equivariance-of-the-twisted-pairing`).

## Implementation notes

The statement is existential, as for constant coefficients
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_adicConstant`): Weil
complexes have no derived tensor product, `Ra^!` or orientation yet, so the derived Poincaré
pairing of `def-pod-derived-poincare-pairing` cannot be written down. It is a node of the
Poincaré duality section, stated here with `sorry` in the form needed by smooth-proper purity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Degreewise Poincaré duality for a lisse Weil sheaf** (blueprint
`thm-pod-degreewise-perfectness-over-a-field` for `K = F` perfect over `ℚ̄_ℓ,X`, with the Frobenius
invariance `thm-pod-equivariance-of-the-twisted-pairing`): for `X₀` smooth, separated, of finite
type and pure dimension `d` over `k₀` and `F` a lisse Weil sheaf on `X₀`, the degreewise
Poincaré pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius. Here `F^∨(d)` is the constant twist of the coefficient
dual `F^∨` by `χ_ℓ(σ)ᵈ`. Properness is not needed. -/
theorem exists_isPerfPair_compactlySupportedCohomology_dual (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    ∃ P : (F.compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
        (((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).carrier
          →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P ((F.compactlySupportedCohomology i).frobenius x)
        ((((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).frobenius y) =
          P x y :=
  sorry

end AlgebraicGeometry.WeilSheaf
