/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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

"Geometrically connected fibres" is Mathlib's `AlgebraicGeometry.GeometricallyConnected G.hom`,
a property of the *morphism* `G ⟶ S`: for every field `K` and every `Spec K ⟶ S` the base change
`G ×[S] Spec K` is connected. Equivalently, by
`AlgebraicGeometry.GeometricallyConnected.iff_geometricallyConnected_fiber`, every fibre of
`G ⟶ S` is geometrically connected over its residue field. It is not a condition on the
underlying space of `G` alone, which need not be connected unless `S` is.

## Main definitions

- `AlgebraicGeometry.IsAbelianScheme`: proper and smooth over `S` with geometrically connected
  fibres.
- `AlgebraicGeometry.IsAbelianScheme.dimAt`: the relative dimension of an abelian scheme `A`
  over `S` at a point `s : S`, that is, the dimension of the fibre `A ×_S Spec κ(s)`.
- `AlgebraicGeometry.IsAbelianScheme.dim`: the dimension of an abelian variety over a field
  `K`, the value of `dimAt` at the unique point of `Spec K`.

## Main statements

- `AlgebraicGeometry.IsAbelianScheme.connectedSpace`: an abelian scheme over a connected base is
  connected; in particular an abelian variety is connected.
- `AlgebraicGeometry.IsAbelianScheme.isLocallyConstant_dimAt`: the relative dimension of an
  abelian scheme is a locally constant function on the base.
- `AlgebraicGeometry.IsAbelianScheme.topologicalKrullDim_eq`: the Krull dimension of an abelian
  variety is the natural number `IsAbelianScheme.dim`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-def-av`: Abelian schemes and abelian varieties.

An *abelian scheme* over a base scheme `S` is a group scheme `G` over `S` which is proper and
smooth over `S` with geometrically connected fibres, that is, `G ×[S] Spec K` is connected for
every field-valued point `Spec K ⟶ S` (Mathlib's `AlgebraicGeometry.GeometricallyConnected G.hom`,
a property of the structure morphism rather than of `G`). Over `S = Spec K` for a field `K` this is
an *abelian variety* over `K`: a proper, smooth and connected group scheme over `K`
(`AlgebraicGeometry.IsAbelianScheme.connectedSpace`). The *relative dimension* of `G` over `S`
at `s : S` is the dimension `AlgebraicGeometry.IsAbelianScheme.dimAt` of the fibre of `G` at `s`;
it is locally constant on `S`. For an abelian variety its value at the unique point of `Spec K`
is the *dimension* `AlgebraicGeometry.IsAbelianScheme.dim` of `G`. -/
class IsAbelianScheme {S : Scheme.{u}} (G : Over S) [GrpObj G] : Prop
    extends IsProper G.hom, Smooth G.hom, GeometricallyConnected G.hom

namespace IsAbelianScheme

variable {S : Scheme.{u}} {K : Type u} [Field K]

/-- The underlying space of an abelian scheme `A` over a connected base `S` is connected: the
structure morphism is open, being smooth, and has geometrically connected fibres, so the
connected components of `A` are those of `S`. -/
instance connectedSpace (A : Over S) [GrpObj A] [IsAbelianScheme A] [ConnectedSpace S] :
    ConnectedSpace A.left :=
  GeometricallyConnected.connectedSpace A.hom
    (isOpenMap_of_generalizingMap A.hom (Flat.generalizingMap A.hom))

/-- The spectrum of a field is connected, being a point. With
`AlgebraicGeometry.IsAbelianScheme.connectedSpace` this makes the underlying space of an
abelian variety connected. -/
instance _root_.AlgebraicGeometry.instConnectedSpaceSpecField : ConnectedSpace (Spec (.of K)) :=
  { toNonempty := inferInstance }

/-- The relative dimension of an abelian scheme `A` over `S` at a point `s : S`: the Krull
dimension of the fibre `A ×_S Spec κ(s)` of the structure morphism at `s`, as a natural number.

`AlgebraicGeometry.IsAbelianScheme.topologicalKrullDim_fiber_eq` says that this really is the
Krull dimension of the fibre: the fibre is nonempty (it has a unit section) and of finite type
over the residue field `κ(s)`, so finite-dimensional. -/
noncomputable def dimAt (A : Over S) [GrpObj A] [IsAbelianScheme A] (s : S) : ℕ :=
  ((topologicalKrullDim (A.hom.fiber s)).unbotD 0).toNat

/-- The Krull dimension of the fibre of an abelian scheme at a point of the base is the natural
number `AlgebraicGeometry.IsAbelianScheme.dimAt`: it is neither `⊥` (the fibre is nonempty,
having a unit section) nor `⊤` (it is of finite type over the residue field). -/
theorem topologicalKrullDim_fiber_eq (A : Over S) [GrpObj A] [IsAbelianScheme A] (s : S) :
    topologicalKrullDim (A.hom.fiber s) = (dimAt A s : ℕ∞) :=
  sorry

/-- The relative dimension of an abelian scheme is locally constant on the base: the structure
morphism is smooth, so its relative dimension at a point of `A` is locally constant on `A`, and
it is proper and surjective with connected fibres, so this descends to the base. -/
theorem isLocallyConstant_dimAt (A : Over S) [GrpObj A] [IsAbelianScheme A] :
    IsLocallyConstant (dimAt A) :=
  sorry

/-- Blueprint `sk-def-av-jacobian`: the dimension of an abelian variety `A` over a field `K`,
that is, its relative dimension `AlgebraicGeometry.IsAbelianScheme.dimAt` at the unique point
of `Spec K`: the Krull dimension of its underlying topological space
(`AlgebraicGeometry.IsAbelianScheme.topologicalKrullDim_eq`). -/
noncomputable def dim (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] : ℕ :=
  dimAt A default

/-- The Krull dimension of an abelian variety is the natural number
`AlgebraicGeometry.IsAbelianScheme.dim`: the fibre of `A` at the unique point of `Spec K` is `A`
itself, and its Krull dimension is neither `⊥` (the variety is nonempty, having a unit section)
nor `⊤` (it is of finite type over `K`). -/
theorem topologicalKrullDim_eq (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianScheme A] :
    topologicalKrullDim A.left = (IsAbelianScheme.dim A : ℕ∞) :=
  sorry

end IsAbelianScheme

end AlgebraicGeometry
