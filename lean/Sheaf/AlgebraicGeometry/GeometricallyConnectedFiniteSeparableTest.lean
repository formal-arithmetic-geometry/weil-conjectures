/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.Separable
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Testing geometric connectedness by finite separable extensions

Source: Stacks Project, Varieties, Lemma Tag 0389
(blueprint: lem-weil-pbc-geometrically-connected-finite-separable-test).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme over a field is geometrically connected precisely when its base change to
 every finite separable field extension is connected.
Source: Stacks Project, Varieties, Lemma Tag 0389
(blueprint: lem-weil-pbc-geometrically-connected-finite-separable-test).

Proof:
1. Geometric connectedness gives connectedness after every field extension, hence every
   finite separable extension (def-pc-geometrically-irreducible).
2. Conversely, assume the finite separable tests hold. Choose a separable closure `ks/k`,
   Galois over `k` and every intermediate field
   (lem-weil-pbc-separable-closure-exists-galois). The automorphisms of `ks/k` act on `Y_ks`
   by base change (def-pc-base-change), contravariantly, and fix its projection `p` to `Y`.
   This projection is surjective (lem-weil-pbc-surjective-base-change).
3. The degree-one test `k/k` makes `Y` nonempty, so `Y_ks` is nonempty too
   (def-weil-connected-scheme, def-weil-pbc-separable-algebraic-extension).
4. If `Y` were not geometrically connected, `Y_ks` would be disconnected: otherwise
   lem-weil-separably-closed-geometrically-connected and
   lem-weil-geometrically-connected-check-after-extension imply geometric connectedness of `Y`.
   Thus write `Y_ks` as the disjoint union of nonempty clopen subsets `Ubar` and `Vbar`.
5. For every quasi-compact open `W` of `Y`, its inverse image `W_ks` is quasi-compact:
   the projection is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence, and `W` is a
   finite union of affine opens (def-weil-finite-type-morphism). Its intersections with
   `Ubar` and `Vbar` are quasi-compact by lem-weil-pbc-closed-in-quasi-compact. By
   lem-weil-pbc-galois-base-change-qc-open-descends they are invariant under automorphisms
   fixing some finite intermediate field `k_W`.
6. Choose a point of `Ubar` and an affine neighbourhood `W0` of its image in `Y`.
   Set `k' = k_W0` and `H = Aut(ks/k')`. This extension is finite and separable algebraic
   by lem-weil-pbc-separable-closure-exists-galois; `W0_ks` intersected with `Ubar` is
   nonempty and `H`-invariant.
7. There are only finitely many `H`-translates of each intersection in step 5.
   Indeed, if the inverses of two automorphisms agree on `k_W`, their translates agree,
   since their quotient fixes `k_W`. There are finitely many embeddings of `k_W` into `ks`
   by lem-weil-pbc-finite-extension-finitely-many-embeddings.
8. Define `U_W` as the intersection of the translates of `W_ks` intersected with `Ubar`,
   and `V_W` as the union of the translates of `W_ks` intersected with `Vbar`.
   By step 7 these operations are finite, giving complementary clopen subsets of `W_ks`.
   They are `H`-invariant by reindexing automorphisms. Also `U_W0` is nonempty, and
   `V_W` contains `W_ks` intersected with `Vbar`.
9. If `W` is contained in `W'`, invariance of `W_ks` and bijectivity of automorphisms
   imply `W_ks` intersected with `U_W'` equals `U_W`, and similarly for `V`.
   For arbitrary `W,W'`, apply this to the quasi-compact open `W` union `W'` to obtain
   compatibility on their overlap.
10. Take the unions of `U_W` and `V_W` over all quasi-compact opens. The compatibility
    gives a complementary open, hence clopen, partition of `Y_ks`, since affine opens
    cover `Y`. Both pieces are `H`-invariant. The first contains `U_W0`; the second
    contains every point of `Vbar` by choosing an affine neighbourhood of its image.
11. Pullback pasting identifies `Y_ks` with the base change of `Y_k'` to `ks`
    (lem-weil-pbc-cartesian-square-pasting, def-pc-fibre-product), with the same `H`-action.
    By lem-weil-pbc-galois-invariant-closed-subset-descends the two pieces descend to closed
    subsets of `Y_k'`. Surjectivity of `Y_ks` to `Y_k'`
    (lem-weil-pbc-surjective-base-change) makes these subsets complementary and nonempty.
    This contradicts the connectedness test for the finite separable extension `k'/k`.
-/
theorem GeometricallyConnected.iff_connectedSpace_finite_separable
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    GeometricallyConnected (Y ↘ Spec (.of k)) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace ↥(pullback (Y ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

end AlgebraicGeometry
