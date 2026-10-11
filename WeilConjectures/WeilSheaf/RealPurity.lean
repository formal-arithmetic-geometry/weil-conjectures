/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Purity of real lisse Weil sheaves on curves

Let `C₀` be a smooth geometrically connected curve over a finite field `k₀` and `𝒢₀` an `ι`-real
lisse Weil sheaf on `C₀`. Every irreducible constituent of `𝒢₀` is punctually `ι`-pure, of its
determinant weight. This is the main theorem of the blueprint section `sec-purity-real-sheaves`,
formalised there on the side of representations of the Weil group
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`); this file states
it for Weil sheaves, with irreducible constituents rendered as irreducible lisse subquotients
`𝒢₂ / 𝒢₁` of lisse Weil subsheaves `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel`: blueprint
  `thm-rp-real-lisse-purity-affine` (`sk-p-real-purity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Purity of real lisse sheaves on curves** (blueprint: `thm-rp-real-lisse-purity-affine`,
`sk-p-real-purity`, of the section `sec-purity-real-sheaves`). Let `C₀` be a smooth geometrically
connected curve over `k₀` and `𝒢₀` an `ι`-real lisse Weil sheaf on `C₀`. Every irreducible
constituent of `𝒢₀`, that is, every irreducible lisse quotient `𝒢₂ / 𝒢₁` of lisse Weil subsheaves
`𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`, is punctually `ι`-pure (of its determinant weight). -/
theorem IsReal.exists_isPunctuallyPureOfWeight_cokernel {ι : PadicAlgCl l →+* ℂ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] {𝒢 : WeilSheaf k₀ l C} (h𝒢 : 𝒢.IsLisse)
    (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C} (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) [Mono i]
    [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse) (hirr : (cokernel i).IsIrreducibleLisse) :
    ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w :=
  sorry

end AlgebraicGeometry.WeilSheaf
