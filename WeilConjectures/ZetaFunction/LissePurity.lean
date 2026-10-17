/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.PoincareDualityLisse
public import WeilConjectures.ZetaFunction.Weights

/-!
# Purity of the cohomology of a lisse pure Weil sheaf on a smooth proper variety

Let `X₀` be a smooth proper `k₀`-scheme of pure dimension `d` and `F` a lisse Weil sheaf on `X₀`,
punctually `ι`-pure of weight `w`. Then `Hⁱ(X₀ ⊗ k̄, F)` is `ι`-pure of weight `w + i`: the
Deligne–Laumon estimate bounds the weights of `H_c^i = Hⁱ` by `w + i`, and Poincaré duality
`H_c^i(F) × H^{2d-i}(F^∨(d)) ⟶ ℚ̄_ℓ`, with `F^∨(d)` lisse and punctually pure of weight
`-w - 2d`, turns the same estimate in degree `2d - i` into the lower bound. This is the absolute
case `Y₀ = Spec k₀` of `prop-zl-smooth-proper-relative-purity`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology`: the upper
  bound for `H_c^i` of a sheaf mixed of weights at most `w`.
- `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_of_isLisse`: purity of `Hⁱ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}

section

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The Deligne–Laumon estimate for compactly supported cohomology: for a separated `k₀`-scheme
`X₀` of finite type and a Weil sheaf `F` mixed of weights at most `w`, `H_c^i(X₀ ⊗ k̄, F)` has
weights at most `w + i` over `k₀` (blueprint `cor-zl-rfshriek-sheaf` for the structure
morphism). -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology {F : WeilSheaf k₀ l X} {w : ℝ}
    (hF : F.IsMixedOfWeightsAtMost ι w) (i : ℤ) :
    (F.compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι (w + i) :=
  sorry

end

/-- **Purity for lisse coefficients** (the absolute case of
`prop-zl-smooth-proper-relative-purity`): for `X₀` smooth and proper of pure dimension `d` over
`k₀` and `F` a lisse Weil sheaf on `X₀`, punctually `ι`-pure of weight `w`, the Frobenius module
`Hⁱ(X₀ ⊗ k̄, F)` is `ι`-pure of weight `w + i` over `k₀`. -/
theorem isPureOfWeightOver_cohomology_of_isLisse (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℤ) :
    (F.cohomology i).IsPureOfWeightOver k₀ ι (w + i) :=
  sorry

end AlgebraicGeometry.WeilSheaf
