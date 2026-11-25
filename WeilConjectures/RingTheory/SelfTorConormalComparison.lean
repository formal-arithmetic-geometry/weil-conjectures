/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
import WeilConjectures.RingTheory.SelfTorConormalComparisonExistence
import WeilConjectures.RingTheory.SelfTorConormalComparisonUnique

/-! # The normalized exterior-to-self-Tor map

For an ideal `I` of a commutative ring `A`, this file defines the canonical map from the
`n`-th exterior power of the conormal module `I/I²` to `Tor_n^A(A/I, A/I)`, characterized by its
Koszul normalization on pure wedges.

## References

* [Stacks, Tag 09PQ]
* [Stacks, Tag 062I]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- For an ideal `I` of `A`, there is a unique map from the `n`-th exterior power of the
conormal module `I/I²` to `Tor_n^A(A/I, A/I)` with Koszul normalization, without regularity
assumptions. -/
theorem existsUnique_selfTor_conormal_comparison (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), IsSelfTorConormalComparison A I n c := by
  obtain ⟨c, hc⟩ := selfTorConormalComparison_exists A I n
  exact ⟨c, hc, fun d hd => (selfTorConormalComparison_unique A I n c d hc hd).symm⟩

/-- The actual normalized exterior-to-self-Tor comparison. The theorem used to select it
fixes its value on all pure wedges, and determines it uniquely. -/
noncomputable def selfTorConormalComparison (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)) :=
  (existsUnique_selfTor_conormal_comparison A I n).exists.choose

/-- The canonical comparison has its defining normalization. -/
theorem selfTorConormalComparison_spec (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    IsSelfTorConormalComparison A I n (selfTorConormalComparison A I n) :=
  (existsUnique_selfTor_conormal_comparison A I n).exists.choose_spec

end AlgebraicGeometry
