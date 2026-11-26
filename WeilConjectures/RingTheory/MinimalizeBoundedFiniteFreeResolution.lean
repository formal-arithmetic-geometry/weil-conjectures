/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.BoundedResolutionCancellationDecreasesRank
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Minimalization of bounded finite free resolutions

Over a local ring, a bounded finite free resolution can be replaced by one of the same length
bound in which every differential has image in the maximal ideal times its target.

## Implementation details

The proof is by induction on the sum of the ranks. A unit matrix coefficient splits off an
identity complex `R → R` in two adjacent degrees (Stacks 00MT); the integer-indexed splitting
lemma is applied after extending the complex by zero in negative degrees. The augmentation
factors through the complement, which is again a finite free resolution. If no unit coefficient
exists, all coefficients lie in the maximal ideal.

## References

* [Stacks, Tags 00MT, 00OA]
-/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat
/-- Repeated cancellation of unit entries in a bounded finite free resolution. -/
theorem minimalize_bounded_finite_free_resolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R)
    (d : ℕ) (P : ProjectiveResolution M)
    (hzero : ∀ i : ℕ, d < i → IsZero (P.complex.X i))
    (hfree : ∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) :
    ∃ Q : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (Q.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (Q.complex.X i) ∧ Module.Free R (Q.complex.X i)) ∧
      (∀ i : ℕ, i < d →
        LinearMap.range (Q.complex.d (i + 1) i).hom ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Q.complex.X i))) := by
  classical
  let rankSum (P : ProjectiveResolution M) : ℕ :=
    ∑ i : Fin (d + 1), Module.finrank R (P.complex.X i.val)
  generalize hn : rankSum P = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hminimal : ∀ i : ℕ, i < d →
        LinearMap.range (P.complex.d (i + 1) i).hom ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i))
    · exact ⟨P, hzero, hfree, hminimal⟩
    · obtain ⟨P', hzero', hfree', hlt⟩ :=
        bounded_resolution_cancellation_decreases_rank M d P hzero hfree hminimal
      exact ih (rankSum P') (by simpa only [← hn] using hlt) P' hzero' hfree' rfl
end ModuleCat
