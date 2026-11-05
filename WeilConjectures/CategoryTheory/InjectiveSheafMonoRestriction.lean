/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Injective abelian sheaves restrict surjectively along monomorphisms

Source: Stacks Project, Cohomology on Sites, Tag 093X.
(blueprint: lem-weil-pbc-injective-sheaf-mono-restriction)
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max w v}]

end CategoryTheory
