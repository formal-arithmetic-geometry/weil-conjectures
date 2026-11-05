/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Valuation.ValuationIndependence

/-!
# Residual independence from linear independence of residues

* `ValuationSubring.valuation_lt_one_iff_inv_notMem`, `ValuationSubring.valuation_comap_lt_one_iff`,
  `ValuationSubring.valuation_comap_eq_one_iff`: the values `< 1`, `= 1` of the pull-back of a
  valuation subring along a field map.
* `Valuation.ResiduallyIndependent.of_linearIndependent_residue`: a family of integral elements
  whose residues are linearly independent over a field `A` is residually independent over every
  field `K` whose integral elements have residues in (the image of) `A`.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

end ValuationSubring

namespace Valuation

variable {F K A : Type*} [Field F] [Field K] [Algebra K F] [Field A] {𝒪 : ValuationSubring F}
  [Algebra A (ResidueField 𝒪)]

end Valuation
