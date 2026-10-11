/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Degree bound from a finite open cover

Source: literature/stacks-project/morphisms.tex, proof of Lemma Tag 03JA,
lines 15507--15518 (blueprint: lem-weil-pbc-finite-open-cover-degree-sum).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- The finite open-cover degree estimate is the parenthetical claim in the
proof of Stacks Project Lemma 03JA. -/
/-- A finite open cover by schemes finite over a field makes the whole scheme
finite over that field, with degree bounded by the sum of the piece degrees.
Source: Stacks Project, Morphisms, proof of Lemma Tag 03JA, lines 15507--15518
(blueprint: lem-weil-pbc-finite-open-cover-degree-sum).

Proof:
1. Put `B i = Γ(U i, ⊤)`, with its `k`-algebra structure induced by
   `(U i).ι ≫ t`. By lem-weil-pbc-finite-over-field-affine-finite-dim each piece
   is affine and finite-dimensional. By
   lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum its spectrum,
   hence the piece itself, is a finite discrete space.
2. The covering makes `T` a finite union of finite sets. Each singleton in `T`
   is open in a covering piece, hence open in `T`; thus `T` is finite discrete.
   When `m = 0`, the covering forces `T` to be empty.
3. By lem-weil-pbc-finite-discrete-scheme-affine, `T` is affine. Give
   `A = Γ(T, ⊤)` the `k`-algebra structure induced by `t` via Spec's global
   sections identification (def-weil-affine-spectrum).
4. Restriction gives a `k`-linear map from `A` to the product of the `B i`:
   functoriality identifies each piece's scalar map with the restriction of
   `t`'s scalar map. This map is injective by the sheaf locality axiom
   (def-pc-scheme). The finite product has dimension the sum of the piece
   dimensions, so `A` is finite-dimensional with dimension at most `∑ i, n i`.
   For the empty cover, sections on the empty scheme form the zero ring.
5. Apply lem-weil-pbc-finite-local-on-target to the single affine open
   `Spec k`: its inverse image `T` is affine and its section algebra `A` is a
   finite `k`-module. Hence `t` is finite (def-weil-finite-integral-morphism),
   with the dimension bound from step 4.
-/
theorem finite_open_cover_degree_sum
    {k : Type u} [Field k] {T : Scheme.{u}}
    (t : T ⟶ Spec (.of k)) (m : ℕ) (U : Fin m → T.Opens)
    (n : Fin m → ℕ)
    (hcover : ⨆ i, U i = ⊤)
    (hfinite : ∀ i : Fin m, IsFinite ((U i).ι ≫ t))
    (hbound : ∀ i : Fin m, ((U i).ι ≫ t).finrankΓ ≤ n i) :
    IsFinite t ∧ t.finrankΓ ≤ ∑ i : Fin m, n i := by
  sorry

end AlgebraicGeometry
