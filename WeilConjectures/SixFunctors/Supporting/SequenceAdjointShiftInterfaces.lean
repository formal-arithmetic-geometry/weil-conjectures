/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
public import WeilConjectures.SixFunctors.Supporting.PurSequenceAdjointResolutionShifts

/-! # Resolution-normalized sequence-site adjoints

Constructions of this file are the published declarations of
`WeilConjectures.SixFunctors.Supporting.PurSequenceAdjointResolutionShifts`, reexported here
unchanged:
`purSequenceShiftedReplacement` (the ordinary shift comparison followed by the shifted given
replacement map), the left and right shift models `PurSequenceLeftShiftModels` and
`PurSequenceRightShiftModels` (coherent integer shifts, reduction and total-limit comparison
squares, shifted quasi-isomorphism and signed degreewise equations), the predicates
`purSequenceRightResolutionCompatibility` and `purSequenceShiftedDegreeCompatibility`, and the
record `PurSequenceAdjointShifts` with the shift compatibility of the same unit and counit.
They are not redeclared, so that one definition per notion is kept.

## References

* [Stacks, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks, Tag 070H](https://stacks.math.columbia.edu/tag/070H)
* [Stacks, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks, Tag 0940](https://stacks.math.columbia.edu/tag/0940)
* [Stacks, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
* [Stacks, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures
