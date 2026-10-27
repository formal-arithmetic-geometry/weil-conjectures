/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalDimensionChartInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.Dimension

/-! # Topological dimension of a quasi-separated algebraic space

Source: Stacks Project, Decent Spaces, Tags 03JX and 0A4J; Properties of Spaces,
Tags 0BAN and 04NA (blueprint: lem-sfb-space-topological-dimension-local-rings).

The unique value supplied by `etaleChart_localDimension` is the dimension of the local
ring at a point. Choosing that unique value introduces no new local-dimension definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The topological dimension is the supremum of the étale-chart local-ring dimensions.
Quasi-separatedness means that the relative diagonal is quasi-compact on scheme tests.
The unique local dimension is chosen from `etaleChart_localDimension`: its specification
says that its image in `WithBot ℕ∞` equals `ringKrullDim` of every chart stalk above the
point. Thus the displayed supremum uses precisely the common values of Tag 04NA.
Both sides are bottom for the empty space, and infinity is allowed.
Source: Stacks Project, Tags 03JX, 0A4J(2), 0BAN(1)=(2), and 04NA
(blueprint: lem-sfb-space-topological-dimension-local-rings).

Proof:
1. Choose a surjective representable étale atlas `a : U → X` from
   `def-trf-algebraic-space`. It is surjective on point classes by
   `def-trf-algebraic-space-jointly-surjective-family`.
2. Two chart points above the same point have a common lift to their scheme fibre
   product (`lem-a1-space-fibre-product-point`). Its projections are étale; dimension
   invariance in `lem-sfb-etale-stalk-invariants` identifies the three stalk dimensions.
   This gives the common value, already packaged by
   `lem-sfb-space-local-dimension-chart-invariance`.
3. By `lem-sfb-quasiseparated-space-sober` and `lem-sc-scheme-sober`, dimensions of
   `|X|` and `U` are computed by strict specialization chains. The noncollapse clause
   of `lem-sfb-quasiseparated-space-etale-specializations` preserves strictness under
   `a`; its lifting clause lifts each chain starting at any point above its last term.
   Hence the sets of finite chain lengths coincide and their dimensions agree.
4. Apply `lem-pc-scheme-dimension-local-rings` to express the dimension of `U` as the
   supremum of its stalk dimensions, without finiteness hypotheses.
5. Each atlas stalk dimension is the local dimension at its image, giving one supremum
   inequality. Surjectivity gives an atlas point above every point of `X`, giving the
   reverse inequality. Combine with steps 3 and 4. Empty suprema are bottom and the
   same upper-bound argument applies to unbounded dimensions. -/
theorem topologicalKrullDim_eq_iSup_etaleLocalRingDimension {S : Scheme.{u}}
    (X : AlgebraicSpace S)
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))) :
    topologicalKrullDim (Point X.obj.obj) =
      ⨆ x : Point X.obj.obj,
        ((etaleChart_localDimension X x).2.2.exists.choose : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
