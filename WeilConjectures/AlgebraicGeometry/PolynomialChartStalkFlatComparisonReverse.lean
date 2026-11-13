/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux

/-! Reverse flatness comparison for a polynomial chart.

## References

* Stacks Project, Tags 00R7 and 00RH.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flatness of the canonical closed-fibre map lifts to the chart stalk map
(Stacks, Tags 00R7 and 00RH). -/
theorem polynomial_chart_stalk_flat_comparison_reverse
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (PolynomialChart.stalkMap f U n e he x).Flat → (e.stalkMap x).hom.Flat := by
  intro hfibre
  exact polynomial_chart_stalk_flat_comparison_reverse_aux f U n e he x
    (Flat.stalkMap f (U.ι x)) hfibre

end AlgebraicGeometry
