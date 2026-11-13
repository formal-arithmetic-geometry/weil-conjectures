/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Dimension
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart

/-! # Quasi-finite polynomial charts at a fibre point

## References

* [Stacks Project, Tag 00QE](https://stacks.math.columbia.edu/tag/00QE)
* [Stacks Project, Tag 00RH](https://stacks.math.columbia.edu/tag/00RH)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A finitely presented affine morphism has a quasi-finite polynomial chart near any point,
with the number of variables equal to the dimension of the fibre at that point. -/
theorem exists_quasiFinite_polynomial_chart
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) :
    ∃ U : X.Opens, IsAffine U.toScheme ∧ y ∈ U ∧
      ∃ (n : ℕ) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T),
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f ∧
      topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_fiber_dimension_nat f y
  obtain ⟨U, hU, hy, e, he₁, he₂, he₃⟩ :=
    exists_quasiFinite_polynomial_chart_data f y n hn
  exact ⟨U, hU, hy, n, e, he₁, he₂, he₃, hn⟩

end AlgebraicGeometry
