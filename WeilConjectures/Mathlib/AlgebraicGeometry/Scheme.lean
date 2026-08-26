/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# A section whose basic open covers its domain is a unit

`AlgebraicGeometry.Scheme.isUnit_of_le_basicOpen`: if `U ≤ X.basicOpen f` for a section
`f : Γ(X, U)`, then `f` is a unit. This is the converse of `Scheme.basicOpen_of_isUnit`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A section of a scheme that is invertible at every point of its domain is a unit.
This is the converse of `Scheme.basicOpen_of_isUnit`. -/
theorem isUnit_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens} {f : Γ(X, U)}
    (h : U ≤ X.basicOpen f) : IsUnit f :=
  X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx ↦ (X.mem_basicOpen f x hx).mp (h hx)

end AlgebraicGeometry.Scheme
