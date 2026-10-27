module

public import Sheaf.AlgebraicTopology.ShuffleHorizontalFaceReindexing
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Vertical deleted vertices of shuffle words

Source: the agent-written vertical-face calculation in the DAG, proof steps 1–10
(blueprint: lem-sfb-shuffle-vertical-face-reindexing). Its application is paragraph (3)
of the latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`; that paragraph
supplies the application only. The requested Weibel §8.5 is unavailable locally.

The word, prefix counts, inversion count, sign and evaluation are the existing
`ShuffleHorizontalFace` declarations, owned by `def-sfb-shuffle-word-combinatorics`.
Boolean `false` is H and `true` is V. Strings retain repetitions; their free integral
basis symbols are `Finsupp.single`. No horizontal-face theorem is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicTopology.ShuffleVerticalFace

open ShuffleHorizontalFace

/-- Vertical labeled vertices, including initial V, terminal V and interior VV cases.
Option-valued access makes both endpoint tests false for the empty word.
Source: the definition of `V_{a,b}` in the agent-written DAG statement
(blueprint: lem-sfb-shuffle-vertical-face-reindexing). -/
def VerticalFace (a b : ℕ) :=
  {p : Word a b × ℕ // p.2 ≤ a + b ∧
    ((p.2 = 0 ∧ p.1.val[0]? = some true) ∨
      (p.2 = a + b ∧ p.1.val[a + b - 1]? = some true) ∨
      (0 < p.2 ∧ p.2 < a + b ∧ p.1.val[p.2 - 1]? = some true ∧
        p.1.val[p.2]? = some true))}

/-- The vertical reindexing, with the exact forward and inverse word rules, evaluated
string identity, inversion counts and Koszul signs. Here `b` is the shorter vertical
degree, so the positive vertical degree of the node is `b+1`. The zero-degree clause
also covers the empty word. The existential equivalence is characterized by its full
forward graph and endpoint/interior inverse rules, rather than chosen arbitrarily.

Source: the agent-written DAG statement and proof steps 1–10
(blueprint: lem-sfb-shuffle-vertical-face-reindexing), supplying the universal shuffle
input to paragraph (3) of the latest blueprint's direct-images proof.

Proof: (1) At an interior VV mark k, put i=A_k and j=B_k. Prefix counting gives
k=i+j, and the adjacent V letters give 1≤j<b+1. Remove the second V of the pair;
exactly one V is lost and all H letters remain.
(2) At the initial or terminal endpoint remove the initial or terminal V, giving
labels 0 and b+1 respectively. These label ranges are disjoint from the interior ones.
(3) For an interior target label j, split its j-th V, counted from one, into VV and
mark the intervening vertex. Writing the shorter word P V Q means that P contains
j-1 V letters; the new mark is |P|+1. Collapse and splitting are mutual inverses.
(4) For labels 0 and b+1 prepend or append V and mark that endpoint. These operations
are inverse to endpoint deletion, proving the equivalence on labeled pairs.
(5) Before an interior omitted vertex the old prefix counts agree with the shorter
ones; afterwards the H count agrees with the next old prefix and the V count is one
less. Deleting input entry j therefore recovers precisely the old evaluated vertices
with entry k omitted.
(6) Initially each remaining V coordinate is shifted by one and deleting input zero
restores it. Terminally all retained prefixes are unchanged, so deleting the last
input entry changes none of their values. Thus the evaluated-string identity holds
at both endpoints too.
(7) An interior removed V contributes precisely its inversions with later H letters.
There are a-i such letters, so I(w)=I(shorter)+(a-i).
(8) An initial removed V contributes a inversions; a terminal V contributes none,
and its marked vertex is k=a+b+1.
(9) Combine k=i+j with the inversion formulas to obtain
s(w)(-1)^k=(-1)^(a+j)s(shorter). At the endpoints use j=0 or j=b+1 and the same
inversion formulas.
(10) With one V no interior VV mark exists, so only endpoint faces remain. With no H,
all inversion counts vanish and k=j. With no V none of the marking tests holds, even
for the empty word. All string comparisons use indices only, so repeated input values
are allowed. Equal strings yield equal basis symbols in the free integral module of
`def-weil-pbc-free-module`. -/
theorem vertical_face_reindexing (a b : ℕ) :
    IsEmpty (VerticalFace a 0) ∧
    ∃ Φ : VerticalFace a (b + 1) ≃ Fin (b + 2) × Word a b,
      (∀ p : VerticalFace a (b + 1),
        (Φ p).1.val = verticalCount p.val.1 p.val.2 ∧
        (Φ p).2.val = p.val.1.val.eraseIdx (min p.val.2 (a + (b + 1) - 1)) ∧
        (0 < p.val.2 ∧ p.val.2 < a + (b + 1) →
          1 ≤ (Φ p).1.val ∧ (Φ p).1.val < b + 1 ∧
          p.val.2 = horizontalCount p.val.1 p.val.2 + (Φ p).1.val ∧
          inversions p.val.1 = inversions (Φ p).2 +
            (a - horizontalCount p.val.1 p.val.2)) ∧
        (p.val.2 = 0 → (Φ p).1.val = 0 ∧
          inversions p.val.1 = inversions (Φ p).2 + a) ∧
        (p.val.2 = a + (b + 1) → (Φ p).1.val = b + 1 ∧
          inversions p.val.1 = inversions (Φ p).2) ∧
        sign p.val.1 * (-1 : ℤ) ^ p.val.2 =
          (-1 : ℤ) ^ (a + (Φ p).1.val) * sign (Φ p).2) ∧
      (∀ q : Fin (b + 2) × Word a b,
        (q.1.val = 0 → (Φ.symm q).val.1.val = true :: q.2.val ∧
          (Φ.symm q).val.2 = 0) ∧
        (q.1.val = b + 1 → (Φ.symm q).val.1.val = q.2.val ++ [true] ∧
          (Φ.symm q).val.2 = a + (b + 1)) ∧
        (0 < q.1.val ∧ q.1.val < b + 1 → ∃ P Q : List Bool,
          q.2.val = P ++ true :: Q ∧ P.count true + 1 = q.1.val ∧
          (Φ.symm q).val.1.val = P ++ true :: true :: Q ∧
          (Φ.symm q).val.2 = P.length + 1)) ∧
      (∀ (X : Type u) (Y : Type v) (x : Fin (a + 1) → X) (y : Fin (b + 1 + 1) → Y)
          (p : VerticalFace a (b + 1)),
        (evaluate p.val.1 x y).eraseIdx p.val.2 =
          evaluate (Φ p).2 x (Fin.removeNth (Φ p).1 y) ∧
        Finsupp.single ((evaluate p.val.1 x y).eraseIdx p.val.2) (1 : ℤ) =
          Finsupp.single (evaluate (Φ p).2 x (Fin.removeNth (Φ p).1 y)) (1 : ℤ)) := by
  sorry

end AlgebraicTopology.ShuffleVerticalFace
