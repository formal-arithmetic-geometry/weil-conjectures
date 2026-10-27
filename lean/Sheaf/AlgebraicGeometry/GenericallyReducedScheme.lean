/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober

/-!
# Generically reduced schemes

Source: Bierstone–Milman–Temkin, Q-universal desingularization, §7, with generic
reducedness interpreted as in the rational-model lemma
(blueprint: def-per-generically-reduced-scheme).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- A scheme is generically reduced if its local ring at every generic point of an
irreducible component is reduced. This does not require reducedness at embedded points.
Source: the generic-reducedness hypothesis of the rational-model construction, guided by
Bierstone–Milman–Temkin, Q-universal desingularization, §7
(blueprint: def-per-generically-reduced-scheme). -/
def IsGenericallyReduced (X : Scheme.{u}) : Prop :=
  ∀ x : X, x ∈ genericPoints X → _root_.IsReduced (X.presheaf.stalk x)

end AlgebraicGeometry
