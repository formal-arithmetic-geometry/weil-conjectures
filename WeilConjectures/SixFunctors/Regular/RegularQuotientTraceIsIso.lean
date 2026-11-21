/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
import WeilConjectures.SixFunctors.Regular.RegularQuotientInjectiveKernel
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint

/-! # Invertibility of the normalized regular quotient coinduction trace

## References

* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* Zheng Lemma 5.22 and Proposition 5.26
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The actual quotient-linear cone trace is an isomorphism on unbounded derived categories. -/
theorem reductionCoinductionTrace_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    IsIso (reductionCoinductionTrace.{u} l E T n) := by
  sorry

end WeilConjectures
