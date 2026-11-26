/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.RingTheory.FilteredColimitPrimeChainContraction
import WeilConjectures.RingTheory.FilteredColimitPrimeChainDimensionBound

/-!
# Prime chains and dimension of filtered ring colimits

A finite strict prime chain in a filtered colimit of rings contracts strictly at some stage, so
the Krull dimension of the colimit is at most the supremum of the stage dimensions.

## Implementation details

For each adjacent pair of primes one chooses an element of the larger one not in the smaller,
represents it at a stage, and uses filteredness to find one stage receiving all of them. For a
chain of length zero any object of the nonempty filtered category works.

## References

* [Stacks, Tag 06LK], converse inequality in the proof
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A finite strict prime chain in a filtered colimit contracts strictly at some stage;
its Krull dimension is therefore bounded by the supremum of the stage dimensions. -/
theorem filteredColimit_prime_chain_and_dimension
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) :
    (∀ (n : ℕ) (p : Fin (n + 1) → Ideal (colimit R : CommRingCat.{u})),
      (∀ j, (p j).IsPrime) → StrictMono p →
      ∃ i : I,
        (∀ j, (Ideal.comap (colimit.ι R i).hom (p j)).IsPrime) ∧
        StrictMono (fun j ↦ Ideal.comap (colimit.ι R i).hom (p j))) ∧
    ringKrullDim (colimit R : CommRingCat.{u}) ≤ ⨆ i : I, ringKrullDim (R.obj i) := by
  exact ⟨filteredColimit_prime_chain_contraction R,
    filteredColimit_prime_chain_dimension_bound R⟩

end CommRingCat
