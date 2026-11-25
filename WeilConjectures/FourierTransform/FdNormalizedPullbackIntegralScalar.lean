/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
public import WeilConjectures.FourierTransform.FdPullbackAugmentationCounitMatching
import WeilConjectures.FourierTransform.FdScalarRoosComparisonIntertwining
import WeilConjectures.FourierTransform.FdPullbackRoosMatchingUniqueness
import WeilConjectures.FourierTransform.FdCoefficientScalarCompletionIdentification

/-! # Integral scalar coherence for fixed normalized pullback components

Integral scalar coherence of the fixed normalized pullback components in the whole-tower
comparison used in the definition of the trace function.

## References

* [Stacks, Tag 0941], [Stacks, Tag 099N]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures
