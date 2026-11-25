/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
import WeilConjectures.RingTheory.SelfTorConormalComparisonHomotopyNormalization

/-!
# Existence of the normalized self-Tor comparison

We show that a normalized comparison map from the exterior powers of the conormal module of
`I` to the self-Tor `Tor_n^A(A/I, A/I)` exists, using a Tate resolution of `A/I`.

## References

* [Stacks, Tag 09PQ]
* [Stacks, Tag 00LS]
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- For every ideal `I` of `A` and every `n`, there is a normalized comparison map from the
`n`-th exterior power of the conormal module of `I` to `Tor_n^A(A/I, A/I)`. -/
theorem selfTorConormalComparison_exists (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), IsSelfTorConormalComparison A I n c := by
  obtain ⟨c, hc⟩ := tate_selfTor_conormal_map A I n
  exact ⟨c, tate_comparison_homotopy_normalization A I n c hc⟩

end AlgebraicGeometry
