module

public import Sheaf.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Local criterion step for the reverse polynomial-chart flatness comparison.
The proof is the Stacks Project local flatness criterion (Tags 00R7 and 00RH):
write the relevant stalks as essentially finitely presented local algebras over
 the base stalk, use flatness over the base and flatness of the closed fibre,
and transport flatness through the canonical fibre-stalk identification.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux) -/
theorem polynomial_chart_stalk_flat_comparison_reverse_aux
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat := by
  sorry

end AlgebraicGeometry
