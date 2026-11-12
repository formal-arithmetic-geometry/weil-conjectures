/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-!
# Riemann–Roch and coherent Serre duality for line bundles on a curve

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus
`g = h¹(X, 𝒪_X)`, and let `ω = Ω¹_{X/k}`. This file collects the statements about line bundles
`ℒ` on `X` proved in `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` into the single
theorem of the blueprint:

* `χ(X, ℒ) = deg ℒ + 1 - g`;
* `H¹(X, ℒ)^∨ ≃ H⁰(X, ω ⊗ ℒ⁻¹)`;
* `deg ω = 2g - 2` and `h⁰(X, ω) = g`;
* if `deg ℒ > 2g - 2`, then `H¹(X, ℒ) = 0` and `h⁰(X, ℒ) = deg ℒ + 1 - g`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.riemannRoch_serreDuality`: the conjunction of these facts.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Serre duality for a line bundle.** On a smooth proper curve `X` over `k`, for an
invertible `ℒ` there is a `k`-linear isomorphism `H¹(X, ℒ)^∨ ≃ H⁰(X, ω ⊗ ℒ⁻¹)`, where
`ω = Ω¹_{X/k}`. This is `AlgebraicGeometry.Scheme.serreDuality` for `q = 1` evaluated at `ℒ`,
composed with the symmetry `ℒ⁻¹ ⊗ ω ≅ ω ⊗ ℒ⁻¹`. -/
theorem Modules.nonempty_dual_H_one_linearEquiv (ℒ : X.Modules) [ℒ.IsInvertible] :
    Nonempty (Module.Dual k (ℒ.H 1) ≃ₗ[k]
      ((X ↘ Spec (.of k)).relativeDifferentials ⊗ ℒᵛ).H 0) := by
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 0 1 rfl
  have := Modules.IsInvertible.sheafOfModules_isInvertible ℒ
  let ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨ℒ, SheafOfModules.IsInvertible.isFiniteLocallyFree ℒ⟩
  exact ⟨(e.app (op ℱ)).toLinearEquiv.trans
    ((Modules.cohomologyFunctor k 0).mapIso (β_ ℱ.objᵛ _)).toLinearEquiv⟩

/-- **Riemann–Roch and coherent Serre duality.** Let `X` be a smooth proper curve over `k` with
`H⁰(X, 𝒪_X) = k`, of genus `g = h¹(X, 𝒪_X)`, let `ω = Ω¹_{X/k}` and let `ℒ` be invertible. Then
1. `χ(X, ℒ) = deg ℒ + 1 - g`;
2. `H¹(X, ℒ)^∨ ≃ H⁰(X, ω ⊗ ℒ⁻¹)` as `k`-vector spaces;
3. `deg ω = 2g - 2`;
4. `h⁰(X, ω) = g`;
5. if `deg ℒ > 2g - 2`, then `H¹(X, ℒ) = 0` and `h⁰(X, ℒ) = deg ℒ + 1 - g`.

The cohomology of `ℒ` is finite-dimensional
(`AlgebraicGeometry.Scheme.Modules.finiteDimensional_H`) and vanishes above degree one
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem Modules.riemannRoch_serreDuality [GlobalSectionsBijective k X] (ℒ : X.Modules)
    [ℒ.IsInvertible] :
    ℒ.eulerChar k = ℒ.degree k + 1 - arithmeticGenus k X ∧
      Nonempty (Module.Dual k (ℒ.H 1) ≃ₗ[k]
        ((X ↘ Spec (.of k)).relativeDifferentials ⊗ ℒᵛ).H 0) ∧
      (X ↘ Spec (.of k)).relativeDifferentials.degree k = 2 * (arithmeticGenus k X : ℤ) - 2 ∧
      (X ↘ Spec (.of k)).relativeDifferentials.finrankH k 0 = arithmeticGenus k X ∧
      (2 * (arithmeticGenus k X : ℤ) - 2 < ℒ.degree k →
        Subsingleton (ℒ.H 1) ∧
          (ℒ.finrankH k 0 : ℤ) = ℒ.degree k + 1 - arithmeticGenus k X) := by
  refine ⟨Modules.eulerChar_eq_degree_add ℒ, Modules.nonempty_dual_H_one_linearEquiv ℒ,
    degree_relativeDifferentials, finrankH_relativeDifferentials_zero_eq_arithmeticGenus,
    fun hd ↦ ⟨?_, finrankH_zero_eq ℒ (by omega)⟩⟩
  have h := Modules.finrankH_one_eq_zero_of_degree (k := k) ℒ (by omega)
  exact Module.finrank_zero_iff.mp h

end AlgebraicGeometry.Scheme
