module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-! Krull-dimension bound for filtered colimits.

Source: Stacks Project, More on Algebra, Tag 06LK.
(blueprint: lem-sc-filtered-colimit-prime-chain-dimension-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- The Krull dimension of a filtered colimit is bounded by the supremum of the
dimensions of its stages. This follows by applying finite prime-chain contraction
to each chain and then taking the supremum in the definition of `ringKrullDim`.
(blueprint: lem-sc-filtered-colimit-prime-chain-dimension-bound) -/
theorem filteredColimit_prime_chain_dimension_bound
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) :
    ringKrullDim (colimit R : CommRingCat.{u}) ≤ ⨆ i : I, ringKrullDim (R.obj i) := by
  sorry

end CommRingCat
