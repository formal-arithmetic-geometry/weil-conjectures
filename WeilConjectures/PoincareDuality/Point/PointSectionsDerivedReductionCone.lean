/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.PoincareDuality.PrincipalDerivedTensorCone
import WeilConjectures.PoincareDuality.Point.PointReductionCoefficientRing

/-! # The cone comparison for point-section reduction

For a complex `C` of modules over the integral coefficient ring, the derived reduction of `C`
modulo the `(n + 1)`st power of the uniformizer is the mapping cone of multiplication by that
power on `C`.

## Implementation details

The coefficient calculation is stated for an arbitrary module complex and is isolated from the
transport along a chosen model of sections. It uses the two-term free resolution of the
principal quotient.

## References

* Stacks Project, Tags 05RT, 06Y6.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- For an integral module complex `C`, the derived reduction of `C` modulo `π ^ (n + 1)`, with
`π` the uniformizer, is the mapping cone of multiplication by `π ^ (n + 1)` on `C`. -/
theorem point_sections_derived_reduction_module_cone (_hl : l ≠ D.p) (n : ℕ)
    (C : CochainComplex (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) :
    Nonempty (((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (pointReductionQuotient l E n)).mapDerivedCategory).obj
        ((pointReductionModuleTensor l E n).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        ((ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) • 𝟙 C))) := by
  exact DerivedCategory.principalDerivedTensorCone (pointReductionQuotient l E n)
    (ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1))
    (pointReductionQuotient_properties l E n).1
    (pointReductionQuotient_properties l E n).2.1
    (pointReductionQuotient_properties l E n).2.2 C

end WeilConjectures
