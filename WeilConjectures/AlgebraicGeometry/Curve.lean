/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ProjectiveMorphism

/-!
# Varieties and curves over a field

Let `k` be a field. A *variety over `k`* is an integral scheme `X` whose structure morphism
`X ⟶ Spec k` is separated and of finite type, a *curve over `k`* is a variety of dimension
one, and a *smooth projective curve over `k`* is a curve whose structure morphism is smooth
and projective.

## Main definitions

- `AlgebraicGeometry.IsVariety` — the class of varieties over a field.
- `AlgebraicGeometry.IsCurve` — the class of curves over a field.
- `AlgebraicGeometry.IsSmoothProjectiveCurve` — the class of smooth projective curves over a
  field.

## Implementation notes

Following the convention of `WeilConjectures/Statement.lean`, a scheme over `k` is encoded by
its structure morphism `f : X ⟶ Spec (.of k)`, and the three notions are classes on `f` in
the style of `AlgebraicGeometry.IsProper`. Being of finite type is spelled out as being
locally of finite type together with quasi-compactness.

`IsVariety.isIntegral` is deliberately not made an instance: the scheme `X` does not
determine the structure morphism `f`, so instance search for `IsIntegral X` would have to
guess both `k` and `f`, which measurably slows down failing searches. Downstream use is
`have := IsVariety.isIntegral f`.

Mathlib has no dimension function for schemes, so dimension one is the condition
`topologicalKrullDim X = 1` on the underlying topological space, which is the supremum of the
lengths of chains of irreducible closed subsets and hence agrees with the supremum of the
Krull dimensions of the local rings of `X`.

## Blueprint

`IsVariety` and `IsCurve` implement `def:pc-curve` and `IsSmoothProjectiveCurve` implements
`def:pc-smooth-projective-curve`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}

/-- A scheme `X` over a field `k` is a **variety** if it is integral and its structure
morphism is separated and of finite type.
(blueprint: `def:pc-curve`, Stacks 020D) -/
@[stacks 020D]
class IsVariety (f : X ⟶ Spec (.of k)) : Prop extends
    IsSeparated f, LocallyOfFiniteType f, QuasiCompact f where
  /-- A variety is integral as a scheme. -/
  isIntegral : IsIntegral X

/-- A scheme `X` over a field `k` is a **curve** if it is a variety of dimension one.
(blueprint: `def:pc-curve`, Stacks 0A23) -/
@[stacks 0A23]
class IsCurve (f : X ⟶ Spec (.of k)) : Prop extends IsVariety f where
  /-- A curve has dimension one. -/
  topologicalKrullDim_eq : topologicalKrullDim X = 1

/-- A scheme `X` over a field `k` is a **smooth projective curve** if it is a curve whose
structure morphism is smooth and projective.
(blueprint: `def:pc-smooth-projective-curve`) -/
class IsSmoothProjectiveCurve (f : X ⟶ Spec (.of k)) : Prop extends
    IsCurve f, Smooth f, IsProjective f where

end AlgebraicGeometry
