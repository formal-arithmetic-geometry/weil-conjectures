/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Unramified morphisms of schemes

Source: Stacks Project, Schemes, Definition 29.35.1 (Tag 02G4), with the
scheme-theoretic diagonal characterization in Lemma 29.35.2 (Tag 02GE)
(blueprint: def-weil-unramified-morphism).

The definition records the node's notion as the conjunction of locally finite type
and an open-immersion diagonal, so it can be used as an ordinary proposition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A scheme morphism is unramified when it is locally of finite type and its
scheme-theoretic diagonal is an open immersion.
Source: Stacks Project, Tag 02G4 and Lemma 02GE.
(blueprint: def-weil-unramified-morphism). -/
def IsUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)

end AlgebraicGeometry
