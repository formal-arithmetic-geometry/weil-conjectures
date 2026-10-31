/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.AlgebraicGeometry.FibreResidueArrow
import WeilConjectures.AlgebraicGeometry.FiniteTypeDimensionFormula
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Coordinate projections lower generic dimension

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-coordinates/lem-fin-coordinate-generic-dimension.md, order 2651
(blueprint: lem-fin-coordinate-generic-dimension).

The strict bound `dim F < n` expresses `dim F ≤ n - 1` with the empty-fibre
convention, including `n = 0`; natural-number truncated subtraction would lose that case.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Coordinate projections from an open subscheme of a closed subscheme of affine space
lower the dimension of the generic fibre by one.

Source: blueprint sec-six-functors-basics/sk-lem-geo-coordinates,
lemma lem-fin-coordinate-generic-dimension, order 2651
(blueprint: lem-fin-coordinate-generic-dimension).

Proof:
1. On every nonempty affine chart Spec R of the integral base S, the zero prime of R[T]
   defines the generic point of the affine line and has residue field K(T), where K is the
   function field of S. The zero primes agree on overlaps. Use
   lem-sc-integral-function-field-affine-fraction for the fraction-field identification.
2. Affine space is locally of finite type over S. Closed and open immersions are locally
   of finite type (lem-weil-pbc-immersion-base-change-lft); composition, cancellation and
   base change (lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-lft-base-change) give this
   property for X over S, the coordinate morphism, and their fibres.
3. By affine-space base change (lemma-nagata-relative-affine-space-charts) and the fibre
   product universal property, the coordinate generic fibre F is the fibre of X_K to A1_K
   over its zero prime, with residue field K(T).
4. At z in F with image x in X_K, lem-sbc-scheme-fibre-stalk-quotient identifies the local
   rings, since the base local ring is K(T) with zero maximal ideal.
   lem-zl-fibre-residue-arrow identifies the residue fields compatibly, giving the actual
   tower K to K(T) to E, where E is the residue field of x.
5. Choose affine neighbourhoods of x and z. By lem-weil-pbc-lft-affine-pairs their algebras
   are finite type over the respective fields. Apply lem-kun-dimension-formula and
   lem-weil-pbc-dimension-at-point-local-ring-trdeg, and then
   lem-weil-pbc-dimension-at-point-open-subspace: writing d for the common local-ring
   dimension, a = trdeg_K E and b = trdeg_K(T) E gives dim_x X_K = d+a and dim_z F = d+b.
   All these quantities are finite.
6. The indeterminate is a transcendence basis of K(T) over K. The tower formula
   lem-kun-transcendence-degree-tower gives a = 1+b.
7. Thus dim_z F + 1 = dim_x X_K ≤ dim X_K ≤ n. For n = 0 any point z would contradict
   nonnegativity, so F is empty.
8. Taking the supremum over z using lem-weil-pbc-dimension-supremum-local-dimensions gives
   the bound. For empty F its dimension is bottom, so the strict bound holds directly.
   The same argument covers empty X_K and does not require reducedness or a Noetherian S. -/
theorem coordinate_generic_fiber_dimension_lt
    {S Y X : Scheme.{u}} [IsIntegral S] (m n : ℕ)
    (e : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S) [IsClosedImmersion e]
    (j : X ⟶ Y) [IsOpenImmersion j]
    (hdim : topologicalKrullDim
      ((j ≫ e ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)).fiber (genericPoint S)) ≤
        (n : WithBot ℕ∞)) (r : Fin m) :
    topologicalKrullDim
      ((j ≫ e ≫ AffineSpace.reindex
        (fun _ : PUnit.{u + 1} ↦ (ULift.up r : ULift.{u} (Fin m))) S).fiber
          (genericPoint (AffineSpace PUnit.{u + 1} S))) < (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
