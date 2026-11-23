/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.WeilSheaf.CurveTopCohomology

/-!
# Weights of `H⁰` and of `H_c²` of a lisse Weil sheaf on a curve

Let `F` be a Weil sheaf on a `k₀`-scheme `X₀` of finite type over `k₀ = 𝔽_q`. Every eigenvalue
`β` of the Frobenius on the global sections `H⁰(X, F)` is, up to the power `deg x`, a local
Frobenius eigenvalue of `F` at a closed point `x`
(`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections`). So if
`F` is punctually of weights `≤ a`, or punctually pure of weight `a`, then so is `H⁰(X, F)`.

If `X₀` is a smooth curve and `F` is lisse, then `H_c²(X, F) = V_{π₁(X)}(-1)` is the Tate twist of
the dual of `H⁰(X, F^∨)` by Poincaré duality. The eigenvalues of the Frobenius on `H⁰(X, F^∨)` are,
up to powers, inverses of local eigenvalues of `F`, so the weights of `H_c²(X, F)` are at most
`a + 2` when `F` is punctually of weights `≤ a`, and `H_c²(X, F)` is pure of weight `a + 2` when
`F` is punctually pure of weight `a`. Neither affineness nor geometric connectedness of `X₀` is
needed here.

## Main statements

All names are in the namespace `AlgebraicGeometry.WeilSheaf`.

- `HasWeightsAtMost.hasWeightsAtMostOver_globalSections`: if `F` is punctually of weights `≤ a`,
  then so is `H⁰(X, F)`.
- `IsPunctuallyPureOfWeight.isPureOfWeightOver_globalSections`: if `F` is punctually pure of
  weight `a`, then so is `H⁰(X, F)`.
- `IsPunctuallyPureOfWeight.isPureOfWeightOver_globalSections_and_compactlySupportedCohomology_two`:
  if `F` is lisse and punctually pure of weight `a`, then `H⁰(X, F)` and `H_c²(X, F)` are pure of
  weights `a` and `a + 2`.

The bound on the weights of `H_c²(X, F)` for `F` lisse and punctually of weights `≤ a` is
`HasWeightsAtMost.compactlySupportedCohomology_two`.

## Implementation details

The statements on `H_c²` rest on `nonempty_equiv_compactlySupportedCohomology_two`, which holds
on any smooth separated curve of finite type over `k₀`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}

/-- If `F` is punctually of weights `≤ a`, then the weights of `H⁰(X, F)` are at most `a`. -/
theorem HasWeightsAtMost.hasWeightsAtMostOver_globalSections {F : WeilSheaf k₀ l X} {a : ℝ}
    (hF : F.HasWeightsAtMost ι a) : F.globalSections.HasWeightsAtMostOver k₀ ι a := by
  intro β hβ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections F hβ
  exact norm_le_rpow_of_norm_pow_degreeOver_le (hF x _ hx)

/-- If `F` is punctually `ι`-pure of weight `a`, then `H⁰(X, F)` is `ι`-pure of weight `a`
(possibly zero). -/
theorem IsPunctuallyPureOfWeight.isPureOfWeightOver_globalSections {F : WeilSheaf k₀ l X}
    {a : ℝ} (hF : F.IsPunctuallyPureOfWeight ι a) :
    F.globalSections.IsPureOfWeightOver k₀ ι a := by
  intro β hβ
  obtain ⟨x, hx⟩ := exists_hasEigenvalue_stalk_of_hasEigenvalue_globalSections F hβ
  exact norm_eq_rpow_of_norm_pow_degreeOver_eq (hF x _ hx)

namespace IsPunctuallyPureOfWeight

/-- If `F` is lisse and punctually `ι`-pure of weight `a` on a smooth curve `X₀`, then
`H⁰(X, F)` and `H_c²(X, F)` are `ι`-pure of weights `a` and `a + 2` respectively (possibly
zero). -/
theorem isPureOfWeightOver_globalSections_and_compactlySupportedCohomology_two
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {a : ℝ} (hw : F.IsPunctuallyPureOfWeight ι a) :
    F.globalSections.IsPureOfWeightOver k₀ ι a ∧
      (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (a + 2) :=
  ⟨hw.isPureOfWeightOver_globalSections,
    WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two ι F hF hw⟩

end IsPunctuallyPureOfWeight

end AlgebraicGeometry.WeilSheaf
