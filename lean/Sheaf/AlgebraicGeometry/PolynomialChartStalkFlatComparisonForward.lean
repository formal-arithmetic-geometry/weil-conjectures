module

public import Sheaf.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! Forward flatness comparison for a polynomial chart.

Source: Stacks Project, Tag 00RH, application of Tag 00R7.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-forward)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flatness of the chart stalk map descends to the canonical closed-fibre map.

The proof uses the local tower of stalk rings, base change to the residue field,
and localization. The canonical fibre stalk identification transports flatness.
Source: Stacks Project, Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-forward) -/
theorem polynomial_chart_stalk_flat_comparison_forward
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (e.stalkMap x).hom.Flat → (PolynomialChart.stalkMap f U n e he x).Flat := by
  sorry

end AlgebraicGeometry
