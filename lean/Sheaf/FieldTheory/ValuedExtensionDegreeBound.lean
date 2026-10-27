/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Sheaf.RingTheory.ValuationComapResidue

import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The fundamental inequality for real-valued field extensions

Source: Temkin, *Stable modification of relative curves*, §2.1, pp. 7–8;
Stacks Project, Tag 0ASH (blueprint: lem-trf-valued-extension-degree-bound).

The base absolute value is the restriction of `v` along `algebraMap F H`. This
parametrizes exactly the pairs of compatible absolute values, including trivial ones.
The value groups are the images of field units in `NNRealˣ`, canonically the positive reals.
The residue scalar action is explicitly the one induced by the canonical residue map.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Valuation

/-- A finite extension with a real-valued nonarchimedean absolute value has finite
residue degree and finite value-group index, whose product is bounded by its degree.
Source: Temkin, §2.1, pp. 7–8; Stacks Project, Tag 0ASH
(blueprint: lem-trf-valued-extension-degree-bound).

Proof plan, following the node and Stacks Tag 0ASH:
1. The valuation integers are the elements of value at most one. Their maximal ideal
   consists of elements of value less than one: an integer is a unit exactly when its
   value is one. The inverse alternative gives the valuation-ring condition
   (`def-trf-valuation-ring`) and shows that its fraction field is the original field.
   Restriction intersects the integer ring and maximal ideal with the base field, so
   the canonical residue map is injective. Values of units form subgroups and restriction
   embeds the base value group into the extension value group.
2. Lift any finite independent residue family of size r to integers b_i of value one,
   and choose c_j representing s distinct value cosets. In a putative nonzero relation
   among b_i*c_j choose a coefficient product a_ij*c_j of maximal absolute value.
   Divide the relation by this product. All terms become integral; terms in the other
   value cosets have value strictly less than one, since equality would identify cosets.
3. Reduction kills those other cosets. The remaining coefficients lie in the base
   integer ring, and the selected coefficient is one. Residue independence contradicts
   the resulting relation. Thus the r*s products are linearly independent over F.
4. Apply `LinearIndependent.fintype_card_le_finrank`
   (`lem-weil-independent-family-card-le-dimension`) to obtain r*s ≤ [H:F].
5. With s=1, adjoining residue elements outside the existing span must stop by [H:F]
   choices; this gives a finite residue basis of size f, with f positive.
6. With r=1 and residue element one, more than [H:F] distinct cosets are impossible.
   Thus the quotient is finite, with positive cardinality e.
7. Apply step 4 to a residue basis and all value-coset representatives to get e*f ≤ [H:F].

`v.valuationSubring.comap (algebraMap F H)` is precisely F's integer ring.
`subgroupOf` realizes the base value group inside the extension value group; hence
`relIndex` is the number of cosets appearing in the node. No completeness or discreteness
is required. Both residue finiteness and quotient finiteness are stated explicitly,
so the zero-on-infinite conventions for `finrank` and `relIndex` lose no information. -/
theorem valued_extension_degree_bound (F : Type u) (H : Type v) [Field F] [Field H]
    [Algebra F H] [FiniteDimensional F H] (v : Valuation H NNReal) :
    @Module.Finite
        (IsLocalRing.ResidueField (v.valuationSubring.comap (algebraMap F H)))
        (IsLocalRing.ResidueField v.valuationSubring) _ _
        (@Algebra.toModule _ _ _ _
          (v.valuationSubring.comapResidueAlgebra (algebraMap F H))) ∧
      Finite ((Units.map (v : H →* NNReal)).range ⧸
        ((Units.map ((v.comap (algebraMap F H)) : F →* NNReal)).range.subgroupOf
          (Units.map (v : H →* NNReal)).range)) ∧
      ((Units.map ((v.comap (algebraMap F H)) : F →* NNReal)).range.relIndex
          (Units.map (v : H →* NNReal)).range) *
        @Module.finrank
          (IsLocalRing.ResidueField (v.valuationSubring.comap (algebraMap F H)))
          (IsLocalRing.ResidueField v.valuationSubring) _ _
          (@Algebra.toModule _ _ _ _
            (v.valuationSubring.comapResidueAlgebra (algebraMap F H))) ≤
        Module.finrank F H := by
  sorry

end Valuation
