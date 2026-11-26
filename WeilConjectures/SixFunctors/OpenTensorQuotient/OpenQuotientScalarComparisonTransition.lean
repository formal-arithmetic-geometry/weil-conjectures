/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonCanonicalTransition

/-! # Transition coherence for the open scalar comparison

We show that the finite open scalar comparison maps commute with the successor maps of the
unrestricted integral quotient complexes.

## Implementation details

Both composites are evaluated on the sheafified pure tensors generating each unrestricted
reduction; the generator formula for `tc.ordinary`, the section formula for `sc.finite`, and
naturality of extension by zero identify both sides with the same coefficient transition.

## References

* Stacks 0E8I, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The finite comparison maps commute with the successor maps of the unrestricted
integral quotient complexes. This is the strict transition part of the normalized
open scalar comparison. -/
theorem openQuotientScalarComparisonTransition
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (level : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ),
      (unrestrictedIntegralComplexFunctor l E X n).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) ≅
        (OpenSemilinearTensor.extensionComplex l E j o).obj
          ((unrestrictedIntegralComplexFunctor l E U n).obj Q))
    (components : ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (i : ℤ),
      ((level n Q).hom.f i) =
        (scalarReductionRestriction l E X n).map ((tc.ordinary n).hom.app (Q.X i)) ≫
          (sc.finite n).hom.app ((scalarReductionExtension l E U n).obj (Q.X i))) :
    ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E U) ℤ) (i : ℤ),
      ((unrestrictedIntegralTransition l E X n).app
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q)).f i ≫
          (level n Q).hom.f i =
        (level (n + 1) Q).hom.f i ≫
          ((OpenSemilinearTensor.extensionComplex l E j o).map
            ((unrestrictedIntegralTransition l E U n).app Q)).f i := by
  intro n Q i
  rw [components n Q i, components (n + 1) Q i]
  exact openQuotientScalarComparisonCanonicalTransition l E j o tc sc n Q i

end WeilConjectures.OpenTensorQuotient
