/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.FieldTheory.Separable

/-!
# Geometric regularity over a separable algebraic extension

Source: Stacks Project, Algebra, Lemma 07QH and Definition 0382
(blueprint: lem-weil-pbc-geometric-regularity-separable-extension).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Geometric regularity of a Noetherian algebra is unchanged when its base field is replaced
by a separable algebraic extension over which the algebra is already defined. The scalar tower
says that the `k`-algebra structure on `R` is the restriction of its `k'`-algebra structure.
Source: Stacks Project, Algebra, Lemma 07QH and Definition 0382
(blueprint: lem-weil-pbc-geometric-regularity-separable-extension).

Proof:
1. Suppose `R` is geometrically regular over `k'`. For any finite purely inseparable `L/k`,
   `L' = k' ⊗[k] L` is a field finite purely inseparable over `k'`
   (lem-weil-pbc-separable-tensor-purely-inseparable-field). Tensor cancellation and symmetry
   identify `L ⊗[k] R` with `L' ⊗[k'] R`
   (lem-weil-pbc-tensor-cancel-base-change). The latter is regular by geometric regularity
   over `k'` (def-weil-pbc-g-ring), proving geometric regularity over `k`.
2. Conversely, suppose `R` is geometrically regular over `k`. The finite intermediate fields
   of the separable algebraic extension `k'/k` form a directed family with union `k'`:
   composita of finite extensions are finite, and each element belongs to its finite simple
   extension. Each intermediate extension is separable (def-weil-pbc-separable-algebraic-extension).
   By lem-weil-pbc-geometrically-regular-over-subfields it suffices to prove the result for
   every finite intermediate extension. Thus assume `k'/k` finite separable.
3. Put `B = R ⊗[k] k'`, with `k'` acting on the second factor. This is finite free over `R`,
   so is Noetherian (lem-weil-pbc-finite-algebra-noetherian). For finite purely inseparable
   `L'/k'`, tensor cancellation identifies `L' ⊗[k'] B` with `L' ⊗[k] R`
   (lem-weil-pbc-tensor-cancel-base-change). Since `L'/k` is finite, the latter is regular
   (lem-weil-pbc-geometrically-regular-finitely-generated-extensions). Thus `B` is geometrically
   regular over `k'` (def-weil-pbc-g-ring).
4. The map `B → R`, sending `r ⊗ c` to `c • r`, is the base change of the multiplication
   `k' ⊗[k] k' → k'`. Indeed tensor cancellation identifies `B` with
   `R ⊗[k'] (k' ⊗[k] k')`, and its base change along multiplication with `R`; the resulting
   map sends `r ⊗ c` to `c • r` (lem-weil-pbc-tensor-cancel-base-change). Multiplication is
   etale, hence smooth (lem-weil-pbc-finite-separable-multiplication-etale). Its base change
   is smooth (lem-weil-pbc-smooth-ring-map-base-change-composition, clause (1)).
5. Geometric regularity over `k'` ascends along this smooth map from the Noetherian algebra
   `B` to `R` (lem-weil-pbc-geometrically-regular-smooth-ascent). Together with the directed
   reduction in step 2 and the reverse implication in step 1, this proves the equivalence. -/
theorem isGeometricallyRegular_iff_of_isSeparable
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]
    [Algebra.IsSeparable k k'] [IsNoetherianRing R] :
    IsGeometricallyRegular k R ↔ IsGeometricallyRegular k' R := by
  sorry

end Algebra
