module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Ascending corrections in a simplicial abelian group

Source: Stacks Project, Tag 08NZ, `lemma-simplicial-group-kan`, ascending correction
paragraph, and Tag 0167, `lemma-relations-face-degeneracy` (1)--(3).
(blueprint: lem-trf-simplicial-abelian-prefix-correction)

The degree is written `m + 2`, so all and only degrees at least two occur.
The auxiliary sequence is constant after its last prescribed transition.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialObject

/-- The actual ascending correction sequence, starting at an arbitrary simplex.
At a transition `r < k`, add the degeneracy of `a r - d r v_r`.
Source: Stacks Project, Tag 08NZ, ascending correction paragraph.
(blueprint: lem-trf-simplicial-abelian-prefix-correction) -/
def abelianPrefixCorrection (X : SimplicialObject AddCommGrpCat.{u}) {m k : ℕ}
    (hk : k ≤ m + 2) (a : Fin k → X _⦋m + 1⦌) (v : X _⦋m + 2⦌) :
    ℕ → X _⦋m + 2⦌
  | 0 => v
  | r + 1 =>
    let w := abelianPrefixCorrection X hk a v r
    if hr : r < k then
      w + X.σ ⟨r, by omega⟩ (a ⟨r, hr⟩ - X.δ ⟨r, by omega⟩ w)
    else w

/-- Ascending correction realizes every compatible prefix and has the stated error identities.
Source: Stacks Project, Tag 08NZ, `lemma-simplicial-group-kan`, ascending paragraph;
Tag 0167, `lemma-relations-face-degeneracy` (1)--(3).
(blueprint: lem-trf-simplicial-abelian-prefix-correction)

Here the node's degree `n ≥ 2` is written `m + 2`. The first conjunct gives every
intermediate prefix, the second gives both lower-face vanishings and the distinguished
face of the correction, and the last two record the initial and terminal simplices.

Proof, following the four steps of the DAG node:
1. Use `def-weil-pbc-simplicial-object` and
   `lem-weil-pbc-simplex-face-face-identity` for `d_i d_r = d_(r-1) d_i` when `i < r`.
   The order-map formulas in Tag 0167 give `d_i s_r = s_(r-1) d_i` and `d_r s_r = id`.
2. Induct on `r ≤ k`, with invariant `d_i v_r = a_i` for `i < r`. At zero this is
   empty, so the initial simplex is arbitrary. The bound `r < k ≤ m + 2` types `s_r`.
3. Compatibility and the face-face identity give
   `d_i e_r = d_(r-1) (a_i - d_i v_r) = 0` for `i < r`. The mixed identities give
   `d_i (s_r e_r) = 0` and `d_r (s_r e_r) = e_r`. All maps are additive.
4. Thus adding `s_r e_r` preserves the earlier faces and sets face `r` to `a_r`.
   Induction proves the intermediate and terminal assertions. For `k = 0` there are
   no transitions and the sequence starts and ends at `v`.
-/
theorem abelianPrefixCorrection_spec (X : SimplicialObject AddCommGrpCat.{u})
    {m k : ℕ} (hk : k ≤ m + 2) (a : Fin k → X _⦋m + 1⦌)
    (ha : ∀ (i j : Fin k), i < j →
      X.δ ⟨i.val, by omega⟩ (a j) = X.δ ⟨j.val - 1, by omega⟩ (a i))
    (v : X _⦋m + 2⦌) :
    (∀ (r : ℕ), r ≤ k → ∀ (i : Fin k), i.val < r →
      X.δ ⟨i.val, by omega⟩ (abelianPrefixCorrection X hk a v r) = a i) ∧
    (∀ (r : Fin k),
      let e := a r - X.δ ⟨r.val, by omega⟩ (abelianPrefixCorrection X hk a v r.val)
      (∀ (i : Fin k), i < r →
        X.δ ⟨i.val, by omega⟩ e = 0 ∧
          X.δ ⟨i.val, by omega⟩ (X.σ ⟨r.val, by omega⟩ e) = 0) ∧
        X.δ ⟨r.val, by omega⟩ (X.σ ⟨r.val, by omega⟩ e) = e) ∧
    abelianPrefixCorrection X hk a v 0 = v ∧
    (∀ (i : Fin k),
      X.δ ⟨i.val, by omega⟩ (abelianPrefixCorrection X hk a v k) = a i) := by
  sorry

end CategoryTheory.SimplicialObject
