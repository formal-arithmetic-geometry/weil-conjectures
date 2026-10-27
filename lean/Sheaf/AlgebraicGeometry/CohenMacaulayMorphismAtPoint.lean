/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth

/-! # Cohen-Macaulayness of a scheme morphism at a point

Source: Stacks Project, More on Morphisms, Tag 045R (definition-CM), expressed
using the Noetherian fibre-stalk convention of lem-sfb-groupoid-cm-locus-descent.
(blueprint: def-sfb-cohen-macaulay-morphism-at-point).

For morphisms with locally Noetherian fibres this is precisely Tag 045R. The
Noetherian condition is included in the predicate so it can be read without an
ambient hypothesis on all fibres. In the groupoid application, local finite
presentation ensures that all fibres are locally Noetherian.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme morphism is Cohen-Macaulay at a point when its local-ring map is flat
and its fibre local ring is Noetherian with depth equal to Krull dimension.
Source: Stacks Project, Tag 045R, using the explicit fibre-stalk convention of
lem-sfb-groupoid-cm-locus-descent. The point of the fibre is `f.asFiber x`, and
depth is coerced into `WithBot ℕ∞` to compare with `ringKrullDim`.
(blueprint: def-sfb-cohen-macaulay-morphism-at-point). -/
def Scheme.Hom.IsCohenMacaulayAtPoint {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ∧
      (IsLocalRing.depth
        (R := (f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- A morphism is Cohen-Macaulay if it is Cohen-Macaulay at every source point.
Source: Stacks Project, Tag 045R (2), with the same explicit Noetherian fibre-stalk
convention as the pointwise predicate.
(blueprint: def-sfb-cohen-macaulay-morphism-at-point). -/
def Scheme.Hom.IsCohenMacaulay {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X, f.IsCohenMacaulayAtPoint x

end AlgebraicGeometry
