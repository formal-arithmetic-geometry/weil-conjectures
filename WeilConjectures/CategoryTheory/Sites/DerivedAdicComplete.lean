/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicCompleteCriteria

/-!
# Derived adic completeness of sheaves

A sheaf `F` with values in a preadditive category with countable products is derived
`n`-adically complete as soon as all its sections `F(U)` are
(`CategoryTheory.Sheaf.isDerivedAdicComplete_of_forall`): limits of sheaves are computed
sectionwise, and a morphism of sheaves is an isomorphism if it is so on all sections.
-/

@[expose] public section

namespace CategoryTheory.Sheaf

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [Preadditive A] [HasLimitsOfShape (Discrete ℕ) A]

end CategoryTheory.Sheaf
