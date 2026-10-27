/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import WeilConjectures.AlgebraicGeometry.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Dimension of a binary product of nonempty algebraic schemes

Source: Stacks Project, varieties.tex, Tag 0B2M,
lemma-dimension-product-locally-algebraic, clause (2).
(blueprint: lem-sfb-scheme-product-dimension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The dimension of a fibre product of two nonempty finite-type schemes over a field
is the sum of their dimensions.

Source: Stacks Project, varieties.tex, Tag 0B2M, clause (2).
(blueprint: lem-sfb-scheme-product-dimension)

Proof:
1. Every module over the field `k` is free and hence flat
   (lem-weil-pbc-module-over-field-flat). The affine criterion
   (lem-weil-pbc-flat-morphism-affine-criterion) makes `a` flat, and base change
   (lem-weil-pbc-flat-morphism-base-change) makes `p : X ×_k Y → Y` flat.
   Finite type is preserved by composition and base change
   (lem-sfb-finite-type-composition-base-change), so `p` and `b` are locally of finite type.
2. At a point `z` of the product above `x` and `y`, invariance of fibre dimension
   (lem-sc-fibre-dimension-after-base-change) gives `dim_z (p⁻¹(y)) = dim_x X`.
   These are the neighbourhood dimensions of def-kun-dimension, not stalk dimensions.
3. Apply lem-sbc-flat-composite-fibre-dimension-at-point to `p` and `b`.
   The fibres over the unique point of `Spec k` identify with the original schemes
   (def-pc-scheme-fibre, def-pc-fibre-product), giving
   `dim_z (X ×_k Y) = dim_x X + dim_y Y`.
4. Every pair `(x,y)` lifts to a product point. Indeed the residue-field tensor product
   is faithfully flat over the first residue field
   (lem-weil-pbc-field-extension-base-change-faithfully-flat), so a prime exists above
   its zero ideal (lem-weil-pbc-faithfully-flat-surjective-spectrum).
   The fibre-product point correspondence (lem-weil-pbc-fibre-product-points) gives
   the lift. In particular the product is nonempty.
5. By lem-kun-dimension-finite-type both dimensions are finite. They are the suprema
   of the point dimensions (lem-weil-pbc-dimension-supremum-local-dimensions), and
   nonemptiness makes these bounded nonempty sets of nonnegative integers. Each
   supremum is attained: otherwise every value is at most one less than the supremum;
   the dimension-zero case is immediate. Lift a pair of maximizing points using step 4.
   Step 3 gives the lower bound by the sum. At every other product point, step 3 gives
   the upper bound by the sum, so taking suprema gives equality. Finally use
   lem-pc-scheme-dimension-local-rings to replace topological dimensions by the
   local-ring suprema of def-pc-dimension.
-/
theorem Scheme.dim_pullback_of_finiteType_over_field
    {k : Type u} [Field k] {X Y : Scheme.{u}} [Nonempty X] [Nonempty Y]
    (a : X ⟶ Spec (CommRingCat.of k)) (b : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [LocallyOfFiniteType b] [QuasiCompact b] :
    (pullback a b).dim = X.dim + Y.dim := by
  sorry

end AlgebraicGeometry
