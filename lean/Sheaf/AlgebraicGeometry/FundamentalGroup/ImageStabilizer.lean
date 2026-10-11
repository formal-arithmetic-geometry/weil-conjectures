/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import Mathlib.GroupTheory.Index

/-!
# The image of the fundamental group of a finite étale cover

Source: SGA 1, Exposé V, Proposition 6.13 and §7, p. 116
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer).

SGA 1 §7 treats locally Noetherian schemes. The same specialization of V.6.13 applies
to arbitrary connected schemes using Stacks Tags 0BNB and 0BND for their Galois category
and fibre functor; no locally Noetherian hypothesis is needed here.
-/

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The fundamental group of a connected finite étale cover has image the stabilizer of
its marked geometric point, an open subgroup whose index is the cardinality of the fibre.
Source: SGA 1, Exposé V, Proposition 6.13 and §7, p. 116
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer).

Proof (the source leaves Proposition 6.13 to the reader):
1. By `lem-galois-pi1-functoriality`, the induced map intertwines the actions through
   `pullbackFiberIso`. The diagonal section of the pullback of the cover takes the unique
   point of the terminal fibre to the marked point. Naturality fixes this section, so the
   image is contained in the stabilizer (`def-galois-categories`, `def-galois-fibre-functor`).
2. Conversely, compose any finite étale cover of `X` with `f`. It is finite étale by
   `lem-weil-pbc-finite-composition` and `lem-weil-pbc-etale-composition-cancellation`.
   Its fibre over `s` is the subset of the composite cover's fibre mapping to the marked
   point. Naturality shows that an element fixing the marked point preserves this subset;
   its inverse does too, giving a permutation (`def-galois-fibre-functor`).
3. These restrictions commute with morphisms and form a natural automorphism of the fibre
   functor over `X`, hence an element of its fundamental group. The equivalence with finite
   locally constant sheaves (`thm-galois-lc-etale`) identifies the two descriptions.
   On pullback covers the restrictions intertwine the actions, so the characterization in
   `lem-galois-pi1-functoriality` and faithful evaluation give the required preimage.
4. Evaluation is continuous into the finite discrete permutation group, so the stabilizer
   is open (`def-galois-fibre-functor`). The cover is a connected object by
   `lem-galois-finite-etale-connected-object` in the Galois category
   `lem-fet-galois-category`. Its fibre is transitive by `lem-galois-transitive`, and
   sending a coset to the translate of the marked point is a bijection with the fibre.
   Thus the index equals its cardinality, including the one-point case. -/
theorem fundamentalGroupMap_range_eq_stabilizer
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type u) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
    let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
    let U := MulAction.stabilizer GY a
    (fundamentalGroupMap (pullbackFiberIso f s) GX GY).range = U ∧
      IsOpen (U : Set GY) ∧ U.index = Nat.card ((fiber (s ≫ f)).obj P) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
