module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.LocalizedChart

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/- The polynomial chart produced by the affine quasi-finite theorem. -/
set_option linter.unusedVariables false in
/-- A prescribed natural fibre dimension yields a quasi-finite polynomial chart.

Source: Stacks Project Tag 00QE and its affine translation in Tag 00RH.
Proof: Identify X and T with Spec B and Spec A, and f with its coordinate ring map.
Finite presentation of f gives finite presentation, hence finite type, of A to B.
The scheme-theoretic fibre is Spec of B tensor the residue field of the image
prime; its distinguished point corresponds to the prime of y. These canonical
homeomorphisms preserve dimension at a point, so hdim is the dimension hypothesis
of `exists_quasiFinite_over_polynomial_algebra` (Tag 00QE). Apply that theorem to
obtain b outside the prime of y and an A-algebra map A[t_1,...,t_n] to B[1/b]
quasi-finite at every prime. Set U = D(b), an affine neighbourhood of y, and take
the spectrum of this map, transporting along the canonical affine isomorphisms
and polynomial variable renaming Fin n to ULift (Fin n). This gives e to relative
affine n-space over T. The A-algebra compatibility gives the required composite
identity. Localization makes B[1/b] finitely presented over A; since the polynomial
ring is finite type over A, `RingHom.FinitePresentation.of_comp_finiteType` gives
finite presentation over A[t]. The affine criterion therefore gives local finite
presentation of e. The affine quasi-finiteness criterion applied to the supplied
primewise quasi-finiteness gives LocallyQuasiFinite e. No dimension existence
result is used here: n and the dimension equality are supplied as hypotheses.
(blueprint: lem-sbc-quasi-finite-polynomial-chart-chart) -/
theorem exists_quasiFinite_polynomial_chart_data
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)) :
    ∃ (U : X.Opens) (_ : IsAffine U.toScheme) (hy : y ∈ U)
      (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T),
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f := by
  let : Algebra Γ(T, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra.FinitePresentation Γ(T, ⊤) Γ(X, ⊤) := f.finitePresentation_appTop
  let : Algebra.FiniteType Γ(T, ⊤) Γ(X, ⊤) := inferInstance
  let q : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom y
  have hdim' := (affine_coordinate_fibre_dimension_eq f y).symm.trans hdim
  obtain ⟨g, hg, φ, hft, hq⟩ :=
    Algebra.exists_quasiFinite_over_polynomial_algebra Γ(T, ⊤) Γ(X, ⊤) q n hdim'
  obtain ⟨e, hefp, heqf, he⟩ := exists_chart_of_localized_polynomial_map f rfl g n φ hft hq
  refine ⟨X.basicOpen g, inferInstance, ?_, e, hefp, heqf, he⟩
  rw [← X.map_PrimeSpectrum_basicOpen_of_affine]
  exact hg

end AlgebraicGeometry
