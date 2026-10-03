/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.KrullDimension

/-!
# Abelian varieties

Following Mathlib, a group scheme over a field `K` is an object `G` of `Over (Spec (.of K))`
equipped with `CategoryTheory.GrpObj G`. An *abelian variety* over `K` is such a group scheme
whose structure morphism is proper and smooth and whose underlying space is connected.

`AlgebraicGeometry.AbelianVariety K` bundles all of this: the object `A.toOver` of
`Over (Spec (.of K))`, its group structure `A.grpObj`, and the three conditions. The group
structure and the conditions are registered as instances, so that for `A : AbelianVariety K`
the group scheme `A.toOver` can be used wherever a group scheme is expected, and its properness,
smoothness and connectedness are found by instance search.

## Main definitions

- `AlgebraicGeometry.AbelianVariety`: a proper, smooth and connected group scheme over `K`.
- `AlgebraicGeometry.AbelianVariety.dim`: the dimension of an abelian variety.

## Main statements

- `AlgebraicGeometry.AbelianVariety.topologicalKrullDim_eq`: the Krull dimension of an abelian
  variety is the natural number `AbelianVariety.dim`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-def-av`: Abelian varieties.

An *abelian variety* over a field `K` is a group scheme over `K` which is proper, smooth and
connected; its *dimension* is `AlgebraicGeometry.AbelianVariety.dim`, the Krull dimension of its
underlying space.

The group scheme is the object `toOver` of `Over (Spec (.of K))` together with its group
structure `grpObj`; the remaining fields are the three conditions on it. -/
structure AbelianVariety (K : Type u) [Field K] where
  /-- The underlying scheme over `K`, as an object of `Over (Spec (.of K))`. -/
  toOver : Over (Spec (.of K))
  /-- The group structure on the scheme. -/
  [grpObj : GrpObj toOver]
  /-- The structure morphism is proper. -/
  [isProper : IsProper toOver.hom]
  /-- The structure morphism is smooth. -/
  [smooth : Smooth toOver.hom]
  /-- The underlying topological space is connected. -/
  [connectedSpace : ConnectedSpace toOver.left]

namespace AbelianVariety

variable {K : Type u} [Field K]

attribute [instance] grpObj isProper smooth connectedSpace

/-- Blueprint `sk-def-av-jacobian`: the dimension of an abelian variety, that is, the Krull
dimension of its underlying topological space, as a natural number.

`AlgebraicGeometry.AbelianVariety.topologicalKrullDim_eq` says that this really is the Krull
dimension: an abelian variety is nonempty and finite-dimensional. -/
noncomputable def dim (A : AbelianVariety K) : ℕ :=
  ((topologicalKrullDim A.toOver.left).unbotD 0).toNat

/-- The Krull dimension of an abelian variety is the natural number
`AlgebraicGeometry.AbelianVariety.dim`: it is neither `⊥` (the variety is nonempty, having a unit
section) nor `⊤` (it is of finite type over `K`). -/
theorem topologicalKrullDim_eq (A : AbelianVariety K) :
    topologicalKrullDim A.toOver.left = (A.dim : ℕ∞) :=
  sorry

end AbelianVariety

end AlgebraicGeometry
