/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension

/-!
# Curves over a field

A *curve over a field `k`* is a separated scheme of finite type over `k` of dimension at most
one, and a *connected curve* is moreover nonempty, connected and of dimension exactly one.
Mathlib has no such class, and the blueprint subsection introducing curves belongs to the
abelian-varieties block; `AlgebraicGeometry.IsCurveOver` and
`AlgebraicGeometry.IsConnectedCurveOver` are the hypothesis bundles that the curve-estimates
block needs, so that the individual statements do not have to repeat them.

The structure morphism is Mathlib's `C ↘ Spec (.of k)`, coming from the class
`AlgebraicGeometry.Scheme.Over`, rather than an explicit `f : C ⟶ Spec (.of k)` argument, and
dimension is `topologicalKrullDim C`, the Krull dimension of the underlying topological space.

Being algebraically closed is *not* part of either class, although the blueprint definition
requires it: the statements that need it carry `[IsAlgClosed k]`.

## Main definitions

- `AlgebraicGeometry.IsCurveOver`: the class of curves over a field.
- `AlgebraicGeometry.IsConnectedCurveOver`: the class of connected curves over a field.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]

/-- A scheme `C` over a field `k` is a *curve over `k`* if it is separated, of finite type
over `k` and of dimension at most one. It may be empty, disconnected, singular, non-reduced or
have zero-dimensional components.
(blueprint: `def-sc-curves`) -/
class IsCurveOver : Prop where
  /-- A curve is separated over its base field. -/
  isSeparated : IsSeparated (C ↘ Spec (.of k))
  /-- A curve is quasi-compact over its base field; together with
  `IsCurveOver.locallyOfFiniteType` this says that it is of finite type. -/
  quasiCompact : QuasiCompact (C ↘ Spec (.of k))
  /-- A curve is locally of finite type over its base field. -/
  locallyOfFiniteType : LocallyOfFiniteType (C ↘ Spec (.of k))
  /-- A curve has dimension at most one. -/
  topologicalKrullDim_le : topologicalKrullDim C ≤ 1

attribute [instance] IsCurveOver.isSeparated IsCurveOver.quasiCompact
  IsCurveOver.locallyOfFiniteType

/-- A *connected curve over `k`* is a curve over `k` that is nonempty, connected and of
dimension exactly one. The nonemptiness is part of Mathlib's `ConnectedSpace`.
(blueprint: `def-sc-curves`) -/
class IsConnectedCurveOver : Prop where
  /-- A connected curve is separated over its base field. -/
  isSeparated : IsSeparated (C ↘ Spec (.of k))
  /-- A connected curve is quasi-compact over its base field. -/
  quasiCompact : QuasiCompact (C ↘ Spec (.of k))
  /-- A connected curve is locally of finite type over its base field. -/
  locallyOfFiniteType : LocallyOfFiniteType (C ↘ Spec (.of k))
  /-- A connected curve is nonempty and connected. -/
  connectedSpace : ConnectedSpace C
  /-- A connected curve has dimension exactly one. -/
  topologicalKrullDim_eq : topologicalKrullDim C = 1

attribute [instance] IsConnectedCurveOver.connectedSpace

instance IsConnectedCurveOver.isCurveOver [h : IsConnectedCurveOver k C] :
    IsCurveOver k C where
  isSeparated := h.isSeparated
  quasiCompact := h.quasiCompact
  locallyOfFiniteType := h.locallyOfFiniteType
  topologicalKrullDim_le := le_of_eq h.topologicalKrullDim_eq

end AlgebraicGeometry
