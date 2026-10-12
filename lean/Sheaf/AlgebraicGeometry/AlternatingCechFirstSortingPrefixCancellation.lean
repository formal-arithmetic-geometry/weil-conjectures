/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

/-!
# Prefix deletions in the first sorting homotopy

Source: Stacks Project, Tag 01FM, equation 20.23.6.1, omitted verification.
(blueprint: lem-pc-alternating-cech-first-sorting-prefix-cancellation)
-/

@[expose] public section

set_option autoImplicit false

universe v w

namespace AlgebraicGeometry.Scheme

open Classical in
/-- The signed prefix-deletion sum cancels exactly the incoming terms whose deleted
label precedes the junction in stable order.

Source: Stacks 01FM, verification of equation 20.23.6.1, prefix-deletion part
of the labelled-deletion argument (details omitted in the source).

Proof: Order labels j by the pairs (t j, j), so all labels are distinct even if
values repeat. The stable-sort filter has one permutation, and the partial-sort
filter has one permutation for each prefix length. For an outgoing term with
r < a, remove j = σ r = τ r. Restrict σ and τ to the other labels and renumber
those labels increasingly. The restricted stable sort is the stable sort of
the face omitting j; the restricted partial sort has prefix length b = a - 1.
The removed label precedes the remaining junction label in the pair order.
Deleting r from the outgoing junction gives exactly the incoming face junction,
as a map to the original labels. Conversely, insert the incoming deleted label
j at its stable rank r before the junction; set a = b + 1 and extend both
permutations. This inverts restriction, including at b = 0 and b = p.
If τ' is the restricted permutation, then sign τ' = (-1)^(r+j) sign τ:
move position r and label j to the end, then restrict, counting the two moves.
Thus the incoming coefficient is (-1)^(j+a-1+r+j) sign τ, the negative of
(-1)^(a+r) sign τ. Sum along this bijection. Each pair evaluates f on the
same map of labels and has opposite integer coefficients, so it cancels.
For a = 0 the outgoing prefix part is empty. Empty I has no input tuple.
(blueprint: lem-pc-alternating-cech-first-sorting-prefix-cancellation) -/
theorem cechFirstSortingPrefixCancellation
    {I : Type v} [LinearOrder I] {B : Type w} [AddCommGroup B]
    (p : ℕ) (t : Fin (p + 2) → I) (f : (Fin (p + 2) → Fin (p + 2)) → B) :
    let before := fun (j : Fin (p + 2)) (σ : Equiv.Perm (Fin (p + 1)))
        (b : Fin (p + 1)) ↦
      t j < t (j.succAbove (σ b)) ∨
        (t j = t (j.succAbove (σ b)) ∧ j < j.succAbove (σ b))
    (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r ≠ σ a) ∧ r.val < a.val then
          (((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) * (-1 : ℤ) ^ r.val) •
            f (cechJunction σ τ a ∘ r.succAbove) else 0) +
      (∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ b : Fin (p + 1),
        ∑ τ : Equiv.Perm (Fin (p + 1)),
          if (cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b) ∧
              before j σ b then
            ((-1 : ℤ) ^ j.val * ((-1 : ℤ) ^ b.val * (Equiv.Perm.sign τ : ℤ))) •
              f (j.succAbove ∘ cechJunction σ τ b) else 0) = 0 := by sorry

end AlgebraicGeometry.Scheme
