/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.DirectImage
public import WeilConjectures.WeilSheaf.GeometricCoinvariants
public import WeilConjectures.WeilSheaf.PoincareDuality
public import WeilConjectures.ZetaLinearAlgebra.Weights

/-!
# The weight estimate for smooth proper varieties

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over the
finite field `k₀ = 𝔽_q`, and let `ι : ℚ̄_ℓ → ℂ` be a field embedding. Deligne's weight estimate
for `Rf_!` (`AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`, blueprint section
`sec-deligne-laumon-general`) applied to the structure morphism of `X₀` and the constant Weil
sheaf, which is punctually pure of weight `0`, shows that `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at
most `i`. Poincaré duality (`AlgebraicGeometry.WeilSheaf.poincareDuality`) turns this upper bound
in degree `2d - i` into a lower bound in degree `i`, so that `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-pure of
weight `i`: every eigenvalue `α` of the geometric Frobenius satisfies `|ι α| = q^{i/2}`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_adicConstant`: the constant Weil sheaf is
  punctually pure of weight `0` (`lem-zl-constant-sheaf-weight-zero`).
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant`:
  `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` has weights at most `i`.
- `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_adicConstant`: `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is
  pure of weight `i` (`prop-weight-purity-ordinary`, `cor-zl-purity-smooth-proper`).
- `AlgebraicGeometry.WeilSheaf.delignePurity`: the five clauses of `thm-weil-deligne-purity` and
  of the subsection `sk-input-weights`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `lem-zl-constant-sheaf-weight-zero`: the constant Weil sheaf `ℚ̄_ℓ` is punctually
`ι`-pure of weight zero: at every closed point the local Frobenius is the identity of the
one-dimensional stalk, whose only eigenvalue `1` has `|ι 1| = 1 = q_x^{0/2}`. -/
theorem isPunctuallyPureOfWeight_adicConstant (ι : PadicAlgCl l →+* ℂ) :
    (adicConstant k₀ l X).IsPunctuallyPureOfWeight ι 0 :=
  sorry

variable {k₀ l} in
/-- A Weil sheaf on `Spec k₀` which is `ι`-mixed of weights at most `w` has global sections of
weights at most `w`: every eigenvalue of the Frobenius on `Γ(Spec k̄, G)` is a local Frobenius
eigenvalue at the unique closed point, of degree one, and the filtration of `G` by punctually
pure sheaves of weights at most `w` bounds it. -/
theorem IsMixedOfWeightsAtMost.hasWeightsAtMostOver_globalSections {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))} {w : ℝ}
    (hG : G.IsMixedOfWeightsAtMost ι w) :
    G.globalSections.HasWeightsAtMostOver k₀ ι w :=
  sorry

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Clause (2) of `sk-input-weights` and of `thm-weil-deligne-purity`: for a separated
`k₀`-scheme `X₀` of finite type, `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-mixed of weights at most `i`:
every eigenvalue `α` of the geometric Frobenius satisfies `|ι α| ≤ q^{i/2}`. This is the
Deligne–Laumon estimate `sk-thm-dl-general-sheaf` for the structure morphism of `X₀` and the
constant Weil sheaf, mixed of weights at most `0`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant (ι : PadicAlgCl l →+* ℂ)
    (i : ℤ) :
    ((adicConstant k₀ l X).compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι i :=
  sorry

end WeilSheaf

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `prop-weight-purity-ordinary` and `cor-zl-purity-smooth-proper` (absolute case of
`sk-prop-smooth-proper-purity`, Step 4): for `X₀` smooth, proper and geometrically connected of
pure dimension `d`, the Frobenius module `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` is `ι`-pure of weight `i`: every
eigenvalue `α` of the geometric Frobenius satisfies `|ι α| = q^{i/2}`.

The upper bound `|ι α| ≤ q^{i/2}` is the Deligne–Laumon estimate
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_adicConstant`)
transported along `H_c^i ≅ Hⁱ`; by Poincaré duality the eigenvalues in degree `2d - i` are the
`q^d / α`, and the upper bound in degree `2d - i` gives `|ι α| ≥ q^{i/2}`. -/
theorem isPureOfWeightOver_cohomology_adicConstant (ι : PadicAlgCl l →+* ℂ) (i : ℤ) :
    ((adicConstant k₀ l X).cohomology i).IsPureOfWeightOver k₀ ι i :=
  sorry

end WeilSheaf

end AlgebraicGeometry
