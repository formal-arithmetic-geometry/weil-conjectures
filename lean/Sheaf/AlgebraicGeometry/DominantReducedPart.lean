/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Irreducible

/-!
# The reduced dominant part of a scheme over a base

Source: ILO, Travaux de Gabber, Expose II 1.2.5--1.2.8, pp. 25--26
(blueprint: def-per-dominant-reduced-part).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The reduced induced closed subscheme on the closure of the union of components dominating
an integral base. For a Noetherian source the union is finite and already closed. Its ideal
is the actual vanishing ideal, so no subscheme is selected by an existence assertion.
Source: ILO II 1.2.5--1.2.8, pp. 25--26 (blueprint: def-per-dominant-reduced-part). -/
noncomputable def dominantReducedPartIdeal {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ Dense (f '' Z)}),
    isClosed_closure⟩

end AlgebraicGeometry
