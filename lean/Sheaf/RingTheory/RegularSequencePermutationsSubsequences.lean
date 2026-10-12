module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.List.OfFn

/-! Equivalence between permutation and subsequence regularity.
Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW.
(blueprint: lem-weil-pbc-regular-sequence-permutations-subsequences-proof).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- Source: Stacks Project, Algebra, Lemma 10.68.10, Tag 07DW.
(blueprint: lem-weil-pbc-regular-sequence-permutations-subsequences-proof).
The equivalence is proved by induction on the length, using the two-element swap lemma.
-/
theorem isRegular_permutations_iff_subsequences
    {R : Type u} [CommRing R] (r : ℕ) (f : Fin r → R)
    (hproper : Ideal.ofList (List.ofFn f) ≠ ⊤) :
    (∀ l : List R, (List.ofFn f).Perm l → IsRegular R l) ↔
      (∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l) := by
  sorry

end RingTheory.Sequence
