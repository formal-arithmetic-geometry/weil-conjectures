/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData

/-! # Normalized finite-Hom quotient comparison laws

This is the quotient-comparison half of the normalized tensor-functor law. -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Every normalized finite coefficient quotient is strong and signed.

Source: the second independent obstruction in the normalized finite-Hom proof. The
quotient calculus tensor model is evaluated on simultaneous K-flat representatives;
scalar association, the coefficient unit, and the signed swap are then localized.
The supplied `RingedDerivedTensorCoherence` witnesses identify the localized
associator, unitors and symmetry with the fixed intrinsic structures. This includes
identity quotients and all zero-complex and empty-scheme cases. -/
theorem finiteHomNormalizedQuotientFunctorLaws
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
      (finiteIntrinsicClosed l E X n).monoidal)
    (hβpro : ∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) :
    ∀ (n m : ℕ) (h : m ≤ n),
      Nonempty (CoefFiniteHomStrong
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)) ∧
      CoefFiniteHomSymmetry
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
        (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
        (coefFiniteHomProTensor l E X h) := by
  sorry

end WeilConjectures
