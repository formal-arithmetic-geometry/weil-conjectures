/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientData

/-! # Canonical level transition for the open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

noncomputable def canonicalOpenQuotientScalarComparisonLevel
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ) :
    (unrestrictedIntegralComplexFunctor l E X n).obj
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ≅
      (OpenSemilinearTensor.extensionComplex l E j o).obj
        ((unrestrictedIntegralComplexFunctor l E U n).obj Q) := by
  let e := Functor.isoWhiskerRight (tc.ordinary n)
      (scalarReductionRestriction l E X n) ≪≫
    Functor.isoWhiskerLeft (scalarReductionExtension l E U n) (sc.finite n)
  exact (NatIso.mapHomologicalComplex e (.up ℤ)).app Q

/-- The canonical finite-level comparison satisfies successor transition coherence.
This is the generator calculation for the unrestricted quotient transition: on each
sheafified pure tensor, both composites apply the same coefficient quotient and the
same normalized extension section. Source: Stacks Tags 0E8I and 0941. -/
theorem openQuotientScalarComparisonCanonicalTransition
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ) (i : ℤ) :
    ((unrestrictedIntegralTransition l E X n).app
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q)).f i ≫
        (canonicalOpenQuotientScalarComparisonLevel l E j o tc sc n Q).hom.f i =
      (canonicalOpenQuotientScalarComparisonLevel l E j o tc sc (n + 1) Q).hom.f i ≫
        ((OpenSemilinearTensor.extensionComplex l E j o).map
          ((unrestrictedIntegralTransition l E U n).app Q)).f i := by
  sorry

end WeilConjectures.OpenTensorQuotient
