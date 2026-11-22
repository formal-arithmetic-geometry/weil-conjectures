/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch

/-!
# Riemann–Roch and Serre duality for line bundles on a curve

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, and let
`ω = Ω¹_{X/k}`. This file gathers the statements about a line bundle `ℒ` on `X` proved in
`WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` into one theorem: `χ(ℒ) = deg ℒ + 1 - g`,
`H¹(X, ℒ)^∨ ≃ H⁰(X, ω ⊗ ℒ⁻¹)`, `deg ω = 2g - 2`, `h⁰(ω) = g`, and, when `deg ℒ > 2g - 2`,
`H¹(X, ℒ) = 0` and `h⁰(ℒ) = deg ℒ + 1 - g`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.riemannRoch_serreDuality`: the theorem above.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Riemann–Roch and Serre duality for line bundles on a curve.** Let `ℒ` be a line bundle on
a smooth proper curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, and let
`ω = Ω¹_{X/k}`. Then `χ(ℒ) = deg ℒ + 1 - g`, `H¹(X, ℒ)^∨ ≅ H⁰(X, ω ⊗ ℒ⁻¹)`, `deg ω = 2g - 2`
and `h⁰(ω) = g`. If moreover `deg ℒ > 2g - 2`, then `H¹(X, ℒ) = 0` and
`h⁰(ℒ) = deg ℒ + 1 - g`. -/
theorem Modules.riemannRoch_serreDuality [GlobalSectionsBijective k X] (ℒ : X.Modules)
    [ℒ.IsInvertible] :
    ℒ.eulerChar k = ℒ.degree k + 1 - arithmeticGenus k X ∧
      Nonempty (Module.Dual k (ℒ.H 1) ≃ₗ[k]
        ((X ↘ Spec (.of k)).relativeDifferentials ⊗ₘ ℒᵛ).H 0) ∧
      (X ↘ Spec (.of k)).relativeDifferentials.degree k = 2 * (arithmeticGenus k X : ℤ) - 2 ∧
      Modules.finrankH k (X ↘ Spec (.of k)).relativeDifferentials 0 = arithmeticGenus k X ∧
      (2 * (arithmeticGenus k X : ℤ) - 2 < ℒ.degree k →
        Subsingleton (ℒ.H 1) ∧
          (Modules.finrankH k ℒ 0 : ℤ) = ℒ.degree k + 1 - arithmeticGenus k X) := by
  refine ⟨Modules.eulerChar_eq_degree_add ℒ, ?_, degree_relativeDifferentials,
    finrankH_relativeDifferentials_zero_eq_arithmeticGenus, fun hd ↦ ?_⟩
  · have := Modules.IsInvertible.sheafOfModules_isInvertible ℒ
    obtain ⟨e⟩ := serreDuality (k := k) (X := X) 0 1 rfl
    let ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
      ⟨ℒ, SheafOfModules.IsInvertible.isFiniteLocallyFree ℒ⟩
    exact ⟨(e.app (op ℱ)).toLinearEquiv ≪≫ₗ
      ((Modules.cohomologyFunctor k 0).mapIso (β_ ℒᵛ _)).toLinearEquiv⟩
  · have hd' : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k := by omega
    exact ⟨Module.finrank_zero_iff.mp (Modules.finrankH_one_eq_zero_of_degree ℒ hd'),
      finrankH_zero_eq ℒ hd'⟩

end AlgebraicGeometry.Scheme
