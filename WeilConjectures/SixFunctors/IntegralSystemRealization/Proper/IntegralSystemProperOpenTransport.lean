/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportCore
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransportPasting

/-! # Transport of intrinsic proper/open pasting

## References

* [Stacks, Tag 0941]
* [Stacks, Tag 03DI]
* [Stacks, Tag 07A7]
* [Stacks, Tags 0F7B--0F7F]
* [Zheng, Construction 4.1 and Lemma 4.10]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the intrinsic proper/open map to any section-normalized operation
models. This assertion has no tensor comparison conclusion. -/
theorem integralSystemProperOpenTransport (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o) :
    Nonempty (ProperOpenCoherence l E o c a b) := by
  obtain ⟨hc⟩ := integralSystemProperOpenTransportCore l E o c a b
  obtain ⟨hp⟩ := integralSystemProperOpenTransportPasting l E o c a hc.gamma b hc.canonical
  exact ⟨{
    gamma := hc.gamma
    adjunct := hc.adjunct
    canonical := hc.canonical
    vertical := hp.vertical
    horizontal := hp.horizontal
    baseChange := hp.baseChange
  }⟩

end WeilConjectures.IntegralSystemRealization
