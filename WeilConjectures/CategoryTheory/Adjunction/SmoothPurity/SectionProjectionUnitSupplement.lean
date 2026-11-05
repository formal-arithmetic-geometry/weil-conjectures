/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.UnitComparison
public import WeilConjectures.CategoryTheory.SectionProjectionUnit

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-section-projection-unit).

# Projection cancellation along a section

Source: blueprint thm-amb-p1-adjunction.proof.md, contraction along the diagonal section.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Adjunction

attribute [local implicit_reducible] TwoSquare

end CategoryTheory.Adjunction
