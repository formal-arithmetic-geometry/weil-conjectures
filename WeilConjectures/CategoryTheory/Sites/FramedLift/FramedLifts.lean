/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection

/-!
# Lifting torsors with a prescribed section

Source: Stacks Project, Tag 03AJ, relative refinement: the lifting-torsor construction
with its chosen lift over an object of the site.
(blueprint: lem-amb-framed-lifts-classification).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {G E Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ E} {d : E ⟶ Q} {w₀ : ι ≫ d = 0}
  {T : C} (hT : IsTerminal T) (hS : (ShortComplex.mk ι d w₀).ShortExact) (U : C)

end CategoryTheory.Sheaf.Torsor

-- Check the axioms of the completed construction.
