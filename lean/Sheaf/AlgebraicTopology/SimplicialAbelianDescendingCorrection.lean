module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Descending corrections in a simplicial abelian group

Source: Stacks Project, Simplicial, Tag 08NZ, `lemma-simplicial-group-kan`, third
proof paragraph (blueprint: lem-trf-simplicial-abelian-descending-correction).

The degree is written `m + 2`, covering precisely the degrees at least two.
The recursion counts corrections from the top; its value at `m + 2 - r` is `w_r`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- The descending correction sequence `w_r`, with initial value `w_(m+2) = v`.
At correction number `t`, the face being set is `m + 2 - t`, and the added term is
`s_(m+1-t) (a_(m+2-t) - d_(m+2-t) w)`. The recursion stops after reaching face `k + 1`.
Only the values with `k ≤ r ≤ m + 2` are part of the sequence in the statement.
Source: Stacks Project, Tag 08NZ, third proof paragraph.
(blueprint: lem-trf-simplicial-abelian-descending-correction) -/
def abelianDescendingCorrection (G : SimplicialObject AddCommGrpCat.{u})
    {m : ℕ} (k : Fin (m + 3))
    (a : (i : Fin (m + 3)) → i ≠ k → G _⦋m + 1⦌)
    (v : G _⦋m + 2⦌) (r : ℕ) : G _⦋m + 2⦌ :=
  Nat.rec v (fun t w ↦
    if ht : t < m + 2 - k.val then
      w + G.σ ⟨m + 1 - t, by omega⟩
        (a ⟨m + 2 - t, by omega⟩ (by
          intro h
          have he : m + 2 - t = k.val := congrArg Fin.val h
          omega) -
          G.δ ⟨m + 2 - t, by omega⟩ w)
    else w) (m + 2 - r)

/-- The defect `b_r = a_r - d_r w_r` at a descending correction, for `r > k`.
Source: Stacks Project, Tag 08NZ, third proof paragraph.
(blueprint: lem-trf-simplicial-abelian-descending-correction) -/
def abelianDescendingDefect (G : SimplicialObject AddCommGrpCat.{u})
    {m : ℕ} (k : Fin (m + 3))
    (a : (i : Fin (m + 3)) → i ≠ k → G _⦋m + 1⦌)
    (v : G _⦋m + 2⦌) (r : Fin (m + 3)) (hr : k < r) : G _⦋m + 1⦌ :=
  a r (ne_of_gt hr) - G.δ r (abelianDescendingCorrection G k a v r.val)

/-- Descending corrections preserve lower faces and realize the upper faces.
Source: Stacks Project, Tag 08NZ, `lemma-simplicial-group-kan`, third proof paragraph.
(blueprint: lem-trf-simplicial-abelian-descending-correction)

Proof, following the six steps of the DAG node:
1. Apply `G` to `lem-weil-pbc-simplex-face-face-identity` to obtain
   `d_i d_j = d_(j-1) d_i` for `i < j`. All operators preserve sums and differences.
2. Descend from `r = m + 2` to `k`, keeping the invariant `d_i w_r = a_i` for
   `i < k` and `i > r`. Initially the upper range is empty and the lower range is `hv`.
3. At `r > k`, compatibility and this invariant give
   `d_i b_r = d_(r-1) (a_i - d_i w_r) = 0` for `i < k`, and
   `d_(i-1) b_r = d_r (a_i - d_i w_r) = 0` for `i > r`.
4. Use `lem-trf-simplicial-mixed-face-degeneracy-identities`: the degeneracy `s_(r-1)`
   therefore has zero faces in those same ranges, and its face `r` is `b_r`.
   If a lower face occurs then `r ≥ 2`, so no degeneracy with negative index is used.
5. Adding this degeneracy preserves the invariant's old faces and sets face `r`, since
   `d_r w_r + b_r = a_r`. Descending induction proves every intermediate invariant
   and all the defect and degeneracy identities.
6. If `k = m + 2`, there are no corrections and only the initial value remains.
   If `k = 0`, all lower-face assertions are empty, including at `r = 1`, where
   the correction uses `s_0` and the adjacent identity still applies.
-/
theorem abelianDescendingCorrection_spec (G : SimplicialObject AddCommGrpCat.{u})
    {m : ℕ} (k : Fin (m + 3))
    (a : (i : Fin (m + 3)) → i ≠ k → G _⦋m + 1⦌)
    (ha : ∀ (i j : Fin (m + 2)), i ≤ j →
      ∀ (hi : i.castSucc ≠ k) (hj : j.succ ≠ k),
        G.δ i (a j.succ hj) = G.δ j (a i.castSucc hi))
    (v : G _⦋m + 2⦌)
    (hv : ∀ (i : Fin (m + 3)), i < k →
      ∀ (hi : i ≠ k), G.δ i v = a i hi) :
    abelianDescendingCorrection G k a v (m + 2) = v ∧
    (∀ (r : Fin (m + 3)), k ≤ r → ∀ (i : Fin (m + 3)), i < k ∨ r < i →
      ∀ (hi : i ≠ k),
        G.δ i (abelianDescendingCorrection G k a v r.val) = a i hi) ∧
    (∀ (r : Fin (m + 3)) (hr : k < r),
      (∀ (i : Fin (m + 2)), i.val < k.val →
        G.δ i (abelianDescendingDefect G k a v r hr) = 0 ∧
        G.δ i.castSucc (G.σ ⟨r.val - 1, by omega⟩
          (abelianDescendingDefect G k a v r hr)) = 0) ∧
      (∀ (i : Fin (m + 3)), r < i →
        G.δ ⟨i.val - 1, by omega⟩ (abelianDescendingDefect G k a v r hr) = 0 ∧
        G.δ i (G.σ ⟨r.val - 1, by omega⟩
          (abelianDescendingDefect G k a v r hr)) = 0) ∧
      G.δ r (G.σ ⟨r.val - 1, by omega⟩
        (abelianDescendingDefect G k a v r hr)) = abelianDescendingDefect G k a v r hr) := by
  sorry

end CategoryTheory.SimplicialObject
