/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealCurve

/-!
# Purity of real lisse Weil sheaves on curves

On a smooth geometrically connected curve `C₀` over a finite field `k₀`, every irreducible
constituent of an `ι`-real lisse Weil sheaf is punctually `ι`-pure of weight its determinant
weight, and every `ι`-real lisse Weil sheaf is `ι`-mixed. The two halves are
`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight` and
`AlgebraicGeometry.WeilSheaf.IsReal.isMixed_of_isLisse`; this file bundles them.

## Main statements

* `AlgebraicGeometry.WeilSheaf.IsReal.purity_and_isMixed`: purity of real lisse Weil sheaves on
  curves (blueprint `theorem-purity-real-sheaves-curves`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]

/-- **Purity of real lisse Weil sheaves on curves** (blueprint:
`theorem-purity-real-sheaves-curves`). Let `C₀` be a smooth geometrically connected curve over
`k₀` and `𝒢` an `ι`-real lisse Weil sheaf on `C₀`.

1. Every irreducible constituent `𝒱 = 𝒢₂ / 𝒢₁` of `𝒢`, for lisse Weil subsheaves
  `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢`, is punctually `ι`-pure of weight `γ = dw_ι(𝒱)`, its determinant weight:
  at every closed point `x`, `rank(𝒱) γ` is the `ι`-weight of `det(F_x | 𝒱_x̄)`
  (`theorem-purity-real-sheaves-curves--1`,
  `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`).
2. `𝒢` is `ι`-mixed (`theorem-purity-real-sheaves-curves--2`,
  `AlgebraicGeometry.WeilSheaf.IsReal.isMixed_of_isLisse`). -/
theorem IsReal.purity_and_isMixed {𝒢 : WeilSheaf k₀ l C} (h𝒢 : 𝒢.IsLisse)
    (hreal : 𝒢.IsReal ι) :
    (∀ {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C} (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) [Mono i] [Mono j],
      𝒢₁.IsLisse → 𝒢₂.IsLisse → (cokernel i).IsIrreducibleLisse →
      ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w ∧ ∀ x : C.finitePoints,
        Module.finrank (PadicAlgCl l) ((cokernel i).stalk x).carrier * w =
          WeilGroup.frobeniusWeight ι ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1)
            (LinearMap.det ((cokernel i).stalk x).frobeniusEnd)) ∧
    𝒢.IsMixed ι :=
  ⟨fun i j _ _ h₁ h₂ hirr ↦
    hreal.exists_isPunctuallyPureOfWeight_cokernel_detWeight h𝒢 i j h₁ h₂ hirr,
    hreal.isMixed_of_isLisse h𝒢⟩

end AlgebraicGeometry.WeilSheaf
