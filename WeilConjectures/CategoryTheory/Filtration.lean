/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Filtered objects of an abelian category

Filtered objects `WeilFilteredObject`, their filtration-preserving morphisms and the finiteness
predicate for decreasing filtrations.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtered object: an object of `C` together with a decreasing filtration. -/
structure WeilFilteredObject (C : Type u) [Category.{v} C] [Abelian C] where
  obj : C
  filtration : DecreasingFiltration obj

namespace WeilFilteredObject

/-- A morphism of filtered objects: a morphism of the underlying objects mapping each
filtration step into the corresponding step. -/
structure Hom (A B : WeilFilteredObject C) where
  hom : A.obj ⟶ B.obj
  preserves : ∀ i : ℤ, ∃ lift : (A.filtration.F i : C) ⟶
    (B.filtration.F i : C),
    lift ≫ (B.filtration.F i).arrow = (A.filtration.F i).arrow ≫ hom

end WeilFilteredObject

namespace DecreasingFiltration

/-- A decreasing filtration is finite if some step is `⊤` and some step is `⊥`. -/
def IsFinite {A : C} (F : DecreasingFiltration A) : Prop :=
  ∃ n m : ℤ, F.F n = ⊤ ∧ F.F m = ⊥

end DecreasingFiltration

end CategoryTheory
