/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Universally fixed points of a scheme group action

Source: Conrad, Reductive group schemes, Section 2.2 (fixed-point functors), and
Corollary 3.3.5, proof, printed p.101 (torus centralizers).
(blueprint: def-sfb-universal-scheme-action-fixed-points).

The action and the test-scheme pullback are the existing internal action and composition.
No representability or reducedness is assumed or chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Points fixed by every group point after every further base change. This set
specifies the fixed subfunctor, rather than just fixed points under the group of
sections over the current test scheme. The definition applies to nonreduced tests,
trivial actions, the empty test scheme and the trivial acting group.

Source: Conrad, Reductive group schemes, Section 2.2 and Corollary 3.3.5, proof,
printed p.101.
(blueprint: def-sfb-universal-scheme-action-fixed-points). -/
def universalActionFixedPoints {S : Scheme.{u}} (R : Grp (Over S))
    (X : Over S) [ModObj R.X X] (U : Over S) : Set (U ⟶ X) :=
  {x | ∀ (V : Over S) (f : V ⟶ U) (t : V ⟶ R.X), t • (f ≫ x) = f ≫ x}

end AlgebraicGeometry
