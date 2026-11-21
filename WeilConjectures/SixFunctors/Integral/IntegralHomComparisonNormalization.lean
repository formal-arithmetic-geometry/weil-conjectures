/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.Integral.IntegralHomComparisonUncurry

/-! # Independence of the normalized integral Hom reduction presentation

## References

* [Stacks, Tag 06YY]
* [Stacks, Tag 08J7]
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe d u
open CategoryTheory Opposite
namespace WeilConjectures

/-- The two normalized presentations give the same evaluation-transpose morphism.
Their tensor orders differ by the signed exchange, so this is an equality of maps
rather than an arbitrary isomorphism between their endpoints. -/
theorem integralHomComparison_normalization
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (K L : completedIntegralDerivedCategory l E X D hl) :
    integralHomReductionComparison D l hl E X n K L =
      IntegralHom.comparison l E X D hl m K L := by
  apply ((m.target.adjunction
    ((integralDerivedReduction l E X D hl n).obj K)).homEquiv _ _).symm.injective
  rw [integralHomComparison_uncurry_eq D l hl E X n a m K L]
  simp [IntegralHom.comparison]

end WeilConjectures
