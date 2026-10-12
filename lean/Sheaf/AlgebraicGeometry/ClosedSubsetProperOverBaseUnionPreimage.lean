/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.ClosedSubsetProperUniversallyClosedImage
import Sheaf.AlgebraicGeometry.ProperCoproduct
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Finite unions and proper preimages of closed subsets proper over a base

Source: Stacks Project, Cohomology of Schemes, Lemma 30.26.6 (Tag 0CYR)
and Lemma 30.26.5 (Tag 0CYQ), part (3)
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-union-preimage).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Finite unions and proper inverse images preserve properness over a base.

Proof of (1), following the node's seven-step proof:
1. Induct on `n` to reduce to two subsets. The empty scheme proves the `n = 0` case,
   using `lem-weil-pbc-closed-subset-proper-over-base-properties`.
2. Take the reduced induced structures (`lem-weil-pbc-reduced-induced-closed-subscheme`).
   Their coproduct map to `X` is finite by `lem-weil-pbc-closed-immersion-finite` and
   `lem-weil-pbc-finite-coproduct`, hence proper and universally closed by
   `lem-weil-pbc-finite-morphism-permanence` and `lem-weil-pbc-proper-fp-permanence`.
3. The coproduct is proper over `S` by `lem-weil-pbc-proper-coproduct`; its whole closed
   subset is proper by `lem-weil-pbc-closed-subset-proper-over-base-properties`.
4. Apply `lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image`; the image
   equals the union since the coprojections cover the coproduct.
Proof of (2):
5. Form the fibre product with the reduced induced structure on `Z`
   (`def-pc-fibre-product`). Its projections are respectively a closed immersion and proper
   by `lem-weil-pbc-closed-immersion-base-change` and `lem-weil-pbc-proper-fp-permanence`.
6. Its image in `X` is precisely the preimage of `Z`, by
   `lem-weil-pbc-fibre-product-points`: compatible points lift because the tensor product
   of their residue fields is nonzero and has a prime ideal.
7. The composite to `S` is proper by `lem-weil-pbc-proper-fp-permanence`. Apply
   `lem-weil-pbc-closed-subset-proper-over-base-properties` to this closed structure.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.26.6 (Tag 0CYR),
proof; Lemma 30.26.5 (Tag 0CYQ), proof of part (3)
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-union-preimage) -/
theorem isClosedSubsetProperOver_union_preimage
    {X S : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] :
    (∀ (n : ℕ) (Z : Fin n → TopologicalSpace.Closeds X),
        (∀ i, IsClosedSubsetProperOver sX (Z i)) →
          IsClosedSubsetProperOver sX (⨆ i, Z i)) ∧
      (∀ {Y : Scheme.{u}} (f : X ⟶ Y) (sY : Y ⟶ S) [LocallyOfFiniteType sY]
          [IsProper f],
        f ≫ sY = sX →
          ∀ (Z : TopologicalSpace.Closeds Y),
            IsClosedSubsetProperOver sY Z →
              IsClosedSubsetProperOver sX (Z.preimage (f := f.base) f.continuous)) := by
  sorry

end AlgebraicGeometry.Scheme
