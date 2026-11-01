/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Classification and normalization of representing traces

Representing traces form a torsor under automorphisms of the representing object.
Fixing the actual natural Hom equivalence removes precisely that freedom.
Source: smooth-purity trace construction, finite diagonal orientation and transported counit.
(blueprint: lem-pur-representing-trace-classification)
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ v₁ v₂
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D) {M : C} {U : D}

end AlgebraicGeometry.ProEtale.CondensedRing
