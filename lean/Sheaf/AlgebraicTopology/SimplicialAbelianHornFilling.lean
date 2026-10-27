/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Horn fillers in simplicial abelian groups

Source: Stacks Project, Simplicial, Tag 08NZ, `lemma-simplicial-group-kan`,
proof, specialized to abelian groups (blueprint: lem-trf-simplicial-abelian-horn-filling).

The simplex dimension is written `n + 1`. The compatibility condition has no equations
when `n = 0`, and uses only the prescribed faces when `n > 0`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Compatible faces of a horn in a simplicial abelian group have a filler.
Source: Stacks Project, Simplicial, Tag 08NZ, `lemma-simplicial-group-kan`, proof
(blueprint: lem-trf-simplicial-abelian-horn-filling).

The simplex dimension is `n + 1`; the family omits face `k`. In dimension at least two,
write an ordered pair of distinct face indices as `i.castSucc < j.succ`, equivalently
`i ≤ j`. The equation is then `d_i a_{j+1} = d_j a_i`.

Proof (the seven DAG steps).
1. Apply the simplicial functor to `lem-weil-pbc-simplex-face-face-identity` to obtain
   the face-face identity. Compute the mixed face-degeneracy identities from the defining
   order maps, as in Stacks 0167; all operators are homomorphisms.
2. In dimension one the single prescribed vertex is filled by its zeroth degeneracy,
   because both faces of that degeneracy are the identity. No compatibility is needed.
3. In higher dimension `N`, start with `v_0 = 0`. Induct for `r < k`, keeping faces `i < r`
   fixed. Put `e_r = a_r - d_r v_r` and `v_{r+1} = v_r + s_r e_r`. Compatibility and
   the face-face identity give `d_i e_r = 0` for `i < r`; the mixed identities preserve
   those faces and set face `r` correctly. The case `r = 0` uses no negative index.
4. Set `w_N = v_k`. Descend through `r > k`, keeping all faces `i < k` and `i > r`
   fixed, with `b_r = a_r - d_r w_r` and `w_{r-1} = w_r + s_{r-1} b_r`.
5. For `i < k < r`, compatibility and the face-face identity give `d_i b_r = 0`.
   The mixed identities therefore preserve the lower faces. If such `i` exists, `r ≥ 2`,
   so the intervening degeneracy index `r - 2` is valid.
6. For `i > r`, the same identities give `d_{i-1} b_r = 0`, preserving upper faces.
   Also `d_r s_{r-1}` is the identity, setting face `r` correctly.
7. Take `u = w_k`. Its invariant prescribes precisely the faces other than `k`.
   If `k = N` there are no descending steps; if `k = 0` there are no lower faces.
   Both inductions use `def-weil-pbc-simplicial-object` and the face-face identity above. -/
theorem exists_horn_filler (G : SimplicialObject AddCommGrpCat.{u})
    (n : ℕ) (k : Fin (n + 2))
    (a : (i : Fin (n + 2)) → i ≠ k → G _⦋n⦌)
    (hcompat : match n, k, a with
      | 0, _, _ => True
      | m + 1, k, a =>
        ∀ (i j : Fin (m + 2)), i ≤ j →
          ∀ (hi : i.castSucc ≠ k) (hj : j.succ ≠ k),
            G.δ i (a j.succ hj) = G.δ j (a i.castSucc hi)) :
    ∃ u : G _⦋n + 1⦌, ∀ (i : Fin (n + 2)) (hi : i ≠ k), G.δ i u = a i hi := by
  sorry

end CategoryTheory.SimplicialObject
