module

public import Sheaf.AlgebraicTopology.ShuffleHorizontalFaceReindexing
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Cancellation at mixed corners of shuffle paths

Source: the agent-written combinatorial input to paragraph (3) of the latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
(blueprint: lem-sfb-shuffle-mixed-corner-cancellation), proof steps 1–6 of the DAG node.
The blueprint gives the application only; the requested Weibel §8.5 is unavailable.

The word, prefix counts, inversion count, integral sign, and evaluation are the existing
`ShuffleHorizontalFace` declarations. Boolean `false` is H and `true` is V. Evaluation
retains repetitions, and `Finsupp.single` is the free integral basis symbol of a string.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicTopology.ShuffleMixedCorner

open ShuffleHorizontalFace

/-- Labeled interior mixed corners; the two accessed letters lie within the word by the
strict bounds on the mark. Source: the definition of `M_{a,b}` in the agent-written DAG
statement (blueprint: lem-sfb-shuffle-mixed-corner-cancellation). -/
def MixedCorner (a b : ℕ) :=
  {p : Word a b × ℕ // 0 < p.2 ∧ p.2 < a + b ∧
    p.1.val[p.2 - 1]? ≠ p.1.val[p.2]?}

open scoped Classical in
/-- The permutation encoding and the fixed-point-free mixed-corner involution, with its
prefix, inversion, evaluated-deletion and sign identities, and the resulting free-module
sum. The permutation is specified by its complete list of values. The involution is
specified by its unchanged mark and by the word obtained by interchanging the adjacent
letters, so neither map is an arbitrary choice. The finiteness witness supplies exactly
the finite set of all labeled corners, including when it is empty.

Source: the agent-written DAG statement and proof steps 1–6
(blueprint: lem-sfb-shuffle-mixed-corner-cancellation), auxiliary to paragraph (3) of the
latest blueprint's direct-images proof.

Proof: (1) List H positions increasingly, then V positions increasingly. These lists
partition the positions and give a permutation. Its only inversions are pairs with the
H position larger than the V position, in bijection with the VH pairs counted by I(w).
(2) Apply `lem-sfb-permutation-sign-inversion-product`, namely
`Equiv.Perm.sign_eq_prod_prod_Ioi`. Every inversion contributes -1 and every other pair
contributes 1, so the sign is (-1)^I(w), also for the empty permutation.
(3) Swap the two different adjacent letters at k-1,k. Counts and the mixed condition
are preserved; swapping twice restores the word and the changed letter precludes a
fixed point. With no H or no V there are no mixed corners.
(4) Prefixes ending before the pair contain neither swapped letter; prefixes ending
after it contain both. Thus only vertex k can change. Deleting it gives the same
coordinate path, hence the same evaluated string for arbitrary, possibly repeated,
input entries.
(5) Inversion pairs disjoint from the swapped positions do not change. Contributions
from any earlier position to the two letters have the same sum, as do contributions
from the two letters to any later position. The pair itself contributes zero for HV
and one for VH, so the inversion counts differ by one and the signed coefficients
are opposite.
(6) The words and marks form a finite set. Pair each labeled corner with its swap:
the deleted basis symbols agree and their coefficients are opposite. Apply
`lem-sfb-finite-involution-sum-zero`, namely `Finset.sum_involution`, in the free
integral module (`def-weil-pbc-free-module`). Coinciding input values do not change
the labeled index set, so no distinctness or nonemptiness assumptions are needed. -/
theorem mixed_corner_cancellation (a b : ℕ) :
    (∀ w : Word a b, ∃ π : Equiv.Perm (Fin (a + b)),
      List.ofFn π =
        ((List.finRange (a + b)).filter (fun i ↦ w.val[i.val]? = some false)) ++
        ((List.finRange (a + b)).filter (fun i ↦ w.val[i.val]? = some true)) ∧
      ((Finset.univ : Finset (Fin (a + b) × Fin (a + b))).filter
        (fun ij ↦ ij.1 < ij.2 ∧ π ij.2 < π ij.1)).card = inversions w ∧
      (π.sign : ℤ) = sign w) ∧
    IsEmpty (MixedCorner 0 b) ∧ IsEmpty (MixedCorner a 0) ∧
    (0 < a + b → ∃ τ : MixedCorner a b → MixedCorner a b,
      (∀ p : MixedCorner a b,
        (τ p).val.2 = p.val.2 ∧
        (τ p).val.1.val =
          (p.val.1.val.set (p.val.2 - 1) (p.val.1.val[p.val.2]?.getD false)).set
            p.val.2 (p.val.1.val[p.val.2 - 1]?.getD false)) ∧
      Function.Involutive τ ∧
      (∀ p : MixedCorner a b, τ p ≠ p) ∧
      (∀ (p : MixedCorner a b) (ℓ : ℕ), ℓ ≤ a + b → ℓ ≠ p.val.2 →
        horizontalCount (τ p).val.1 ℓ = horizontalCount p.val.1 ℓ ∧
        verticalCount (τ p).val.1 ℓ = verticalCount p.val.1 ℓ) ∧
      (∀ p : MixedCorner a b,
        (inversions (τ p).val.1 = inversions p.val.1 + 1 ∨
          inversions p.val.1 = inversions (τ p).val.1 + 1) ∧
        sign (τ p).val.1 * (-1 : ℤ) ^ p.val.2 =
          -(sign p.val.1 * (-1 : ℤ) ^ p.val.2)) ∧
      (∀ (X : Type u) (Y : Type v) (x : Fin (a + 1) → X) (y : Fin (b + 1) → Y)
          (p : MixedCorner a b),
        (evaluate (τ p).val.1 x y).eraseIdx p.val.2 =
          (evaluate p.val.1 x y).eraseIdx p.val.2) ∧
      ∃ hM : (Set.univ : Set (MixedCorner a b)).Finite,
        ∀ (X : Type u) (Y : Type v) (x : Fin (a + 1) → X) (y : Fin (b + 1) → Y),
          (∑ p ∈ hM.toFinset, (sign p.val.1 * (-1 : ℤ) ^ p.val.2) •
            Finsupp.single ((evaluate p.val.1 x y).eraseIdx p.val.2) (1 : ℤ)) =
            (0 : List (X × Y) →₀ ℤ)) := by
  sorry

end AlgebraicTopology.ShuffleMixedCorner
