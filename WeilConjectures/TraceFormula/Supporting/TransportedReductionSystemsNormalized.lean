/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

import WeilConjectures.TraceFormula.Supporting.TransportedReductionPullbackNormalized
import WeilConjectures.TraceFormula.Supporting.TransportedReductionScalarNormalized

/-! # Normalization of the two transported reduction systems

Exact inverse image and ramified coefficient change preserve normalization of strict derived
reduction systems.

## Implementation details

Pullback normalization uses `SemilinearSections.normalized_inverseImage_closure`, identifying the
pulled coefficient rings with the target constant quotient rings. Scalar normalization goes
through `coefficientExtensionReductionModel` and the unique counit-compatible comparison of
universal pairs. The construction uses balanced association of actual quotient tensors; it does
not assume the quotient-ring inclusions flat or of finite Tor dimension.

## References

* Stacks Project, Tags 07A4, 06YY and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Exact inverse image and ramified coefficient change preserve normalization of
an ambient object's strict derived reduction system. -/
theorem transportedReductionSystems_normalized
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) := by
  exact ⟨transportedReductionSystems_pullback_normalized l E f _hlX _hlY SY,
    transportedReductionSystems_scalar_normalized l E L ι _hlY SY⟩

end WeilConjectures
