/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Coefficient comparisons, units of derived adjunctions and the exchange maps

Let `ρ : Λ →+* Λ'` be a morphism of coefficient rings. The coefficient comparison
`Res ⋙ Rf_* ≅ Rf_* ⋙ Res` of the unbounded derived direct image is the mate of the coefficient
comparison of the derived pullback, both for `Lf^* ⊣ Rf_*` and for `D(f^*) ⊣ Rf_*`
(`WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar`). Consequently:

- the derived base change map `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is compatible with the
  coefficient comparisons (`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_restrictScalars`);
- for finite `Λ`, the comparison of derived lower shrieks along a refinement of
  compactifications is compatible with the coefficient comparisons, see
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison_app_restrictScalars`.
-/
