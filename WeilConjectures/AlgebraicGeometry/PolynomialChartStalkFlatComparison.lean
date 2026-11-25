/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonForward
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverse

/-! # Flatness comparison for a polynomial chart and its closed fibre

## References

* Stacks Project, Tags 00R7 and 00RH.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A stalk map of a chart is flat precisely when its closed-fibre stalk map is flat
(Stacks, Tags 00RH and 00R7). -/
theorem polynomial_chart_stalk_flat_comparison
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (e.stalkMap x).hom.Flat ↔ (PolynomialChart.stalkMap f U n e he x).Flat := by
  constructor
  · exact polynomial_chart_stalk_flat_comparison_forward f U n e he x
  · exact polynomial_chart_stalk_flat_comparison_reverse f U n e he x

end AlgebraicGeometry
