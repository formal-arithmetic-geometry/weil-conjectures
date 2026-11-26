/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.OfFn
import WeilConjectures.RingTheory.RegularSequencePermutationsSubsequences
import WeilConjectures.RingTheory.RegularSequenceSubsequencesPolynomial

/-!
# Regular sequences multiplied by polynomial variables

For a finite family generating a proper ideal, regularity of all permutations, of all
order-preserving subsequences, and of the sequence multiplied by distinct polynomial variables
are equivalent.

## Implementation details

Permutations and subsequences are compared by induction on the length, using the two-element
swap lemma in a suitable quotient. For polynomial variables, put `J_i = (f_j X_j : j < i)`: a
polynomial lies in `J_i` exactly when each coefficient of exponent `E` lies in
`I_E = (f_j : j < i, E_j > 0)`, so multiplication by `f_i X_i` is injective modulo `J_i` exactly
when multiplication by `f_i` is injective modulo every `I_E`, which is a subsequence condition.

## References

* [Stacks, Tag 07DW]
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- For a finite family generating a proper ideal, regularity of all permutations, regularity of
all order-preserving subsequences, and regularity after multiplying by distinct polynomial
variables are equivalent. `List.ofFn f` lists the family in increasing index order. -/
theorem isRegular_permutations_subsequences_polynomial_iff
    {R : Type u} [CommRing R] (r : ℕ) (f : Fin r → R)
    (hproper : Ideal.ofList (List.ofFn f) ≠ ⊤) :
    ((∀ l : List R, (List.ofFn f).Perm l → IsRegular R l) ↔
      (∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l)) ∧
    ((∀ l : List R, l.Sublist (List.ofFn f) → IsRegular R l) ↔
      IsRegular (MvPolynomial (Fin r) R)
        (List.ofFn (fun i : Fin r ↦ MvPolynomial.C (f i) * MvPolynomial.X i))) := by
  exact ⟨isRegular_permutations_iff_subsequences r f hproper,
    isRegular_subsequences_iff_polynomial_variables r f hproper⟩

end RingTheory.Sequence
