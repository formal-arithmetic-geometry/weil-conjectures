/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import Sheaf.Topology.DimensionSupremumLocalDimensions
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Uniform dimension bound for fibres of a finite-type morphism

Source: Stacks Project, Morphisms, Tag 0A3V,
lemma-morphism-finite-type-bounded-dimension
(blueprint: lem-fin-finite-type-fibre-dimension-bound).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-type morphism with quasi-compact target has a uniform finite bound on the
Krull dimensions of its scheme-theoretic fibres, including empty fibres of dimension bottom.

Source: Stacks Project, Morphisms, Tag 0A3V,
lemma-morphism-finite-type-bounded-dimension.
(blueprint: lem-fin-finite-type-fibre-dimension-bound)

Proof:
1. Finite type means locally of finite type and quasi-compact. Apply
   `lem-weil-pbc-quasi-compact-morphism-preimage-qc-open` to the whole quasi-compact target
   to obtain quasi-compactness of X. If X is empty, choose d = 0.
2. Around each x choose affine charts U = Spec B and V = Spec A with f(U) contained in V
   and B a finite-type A-algebra (`def-weil-finite-type-morphism`). The affine fibre-product
   formula (`lem-weil-pbc-fibre-product-affine-spectra`) identifies the chart fibre with
   Spec of B tensor the residue field. It is affine and quasi-compact
   (`lem-weil-pbc-affine-scheme-qcqs`), and finite type over that field, so
   `lem-kun-dimension-finite-type` gives finite dimension. By
   `lem-weil-pbc-open-preimage-fibre-product` and `def-pc-fibre-product`, this chart fibre is
   the open inverse image of U in the full fibre. Local dimension agrees there by
   `lem-weil-pbc-dimension-at-point-open-subspace`. Thus the local fibre dimension e(x)
   is a finite nonnegative integer (`def-kun-topological-dimension-at-point`).
3. For each n, the locus W_n where e(x) is at most n is open. On an affine chart,
   `lem-sbc-affine-coordinate-fibre-dimension` identifies e(x) with the coordinate-ring
   fibre's local dimension. Apply `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`
   at x with d = e(x), and use open-subspace invariance of local dimension. This gives
   an open neighbourhood contained in W_n for every x in W_n; the charts cover X.
4. The increasing opens W_n cover X, so quasi-compactness
   (`def-weil-pbc-quasi-compact-scheme`) gives a finite subcover. Take d to be the maximum
   of its indices and zero. Then e(x) is at most d everywhere. The fibre's points are
   the points of the inverse image (`def-pc-scheme-fibre`), so
   `lem-weil-pbc-dimension-supremum-local-dimensions` bounds each fibre's global dimension
   by d. For an empty fibre the supremum is bottom, hence also at most d. -/
theorem exists_fibre_dimension_bound {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] :
    ∃ d : ℕ, ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
