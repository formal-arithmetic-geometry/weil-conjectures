/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.KrullDimension

/-!
# Abelian schemes and abelian varieties

Following Mathlib, a group scheme over a base scheme `S` is an object `G` of `Over S` equipped
with `CategoryTheory.GrpObj G`. An *abelian scheme* over `S` is a group scheme over `S` whose
structure morphism is proper and smooth with geometrically connected fibres. An *abelian
variety* over a field `K` is an abelian scheme over `Spec K`.

`AlgebraicGeometry.IsAbelianScheme G` is a predicate on the group scheme `G`: it takes the group
structure `[GrpObj G]` as a parameter, so that a declaration about abelian schemes reads
`[GrpObj G] [IsAbelianScheme G]`.

## Main definitions

- `AlgebraicGeometry.IsAbelianScheme`: proper and smooth over `S` with geometrically connected
  fibres.
- `AlgebraicGeometry.IsAbelianScheme.dim`: the dimension of an abelian variety.

## Main statements

- `AlgebraicGeometry.IsAbelianScheme.connectedSpace`: an abelian variety is connected.
- `AlgebraicGeometry.IsAbelianScheme.topologicalKrullDim_eq`: the Krull dimension of an abelian
  variety is the natural number `IsAbelianScheme.dim`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-def-av`: Abelian schemes and abelian varieties.

An *abelian scheme* over a base scheme `S` is a group scheme `G` over `S` which is proper and
smooth over `S` with geometrically connected fibres. Over `S = Spec K` for a field `K` this is
an *abelian variety* over `K`: a proper, smooth and connected group scheme over `K`
(`AlgebraicGeometry.IsAbelianScheme.connectedSpace`), whose *dimension* is
`AlgebraicGeometry.IsAbelianScheme.dim`, the Krull dimension of its underlying space. -/
class IsAbelianScheme {S : Scheme.{u}} (G : Over S) [GrpObj G] : Prop
    extends IsProper G.hom, Smooth G.hom, GeometricallyConnected G.hom

namespace IsAbelianScheme

variable {K : Type u} [Field K]

/-- The underlying space of an abelian variety is connected, being geometrically connected over
the one-point space `Spec K`. -/
instance connectedSpace (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] :
    ConnectedSpace A.left :=
  GeometricallyConnected.connectedSpace_of_subsingleton A.hom

/-- Blueprint `sk-def-av-jacobian`: the dimension of an abelian variety, that is, the Krull
dimension of its underlying topological space, as a natural number.

`AlgebraicGeometry.IsAbelianScheme.topologicalKrullDim_eq` says that this really is the Krull
dimension: an abelian variety is nonempty and finite-dimensional. -/
noncomputable def dim (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] : ℕ :=
  ((topologicalKrullDim A.left).unbotD 0).toNat

/-- The Krull dimension of an abelian variety is the natural number
`AlgebraicGeometry.IsAbelianScheme.dim`: it is neither `⊥` (the variety is nonempty, having a
unit section) nor `⊤` (it is of finite type over `K`). -/
theorem topologicalKrullDim_eq (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] :
    topologicalKrullDim A.left = (IsAbelianScheme.dim A : ℕ∞) :=
  sorry

end IsAbelianScheme

end AlgebraicGeometry
