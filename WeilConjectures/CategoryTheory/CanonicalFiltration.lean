/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration

public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Filtrations of objects in an abelian category

Source: Stacks Project, Homology, Definition 12.19.1 (Tag 0121)
(blueprint: def-sp-filtration).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DecreasingFiltration

/-- Compatibility accessor for the filtration API; the filtration is upstream's. -/
@[simp] abbrev step {A : C} (F : DecreasingFiltration A) := F.F

omit [Abelian C] in
/-- Compatibility form of upstream's antitonicity theorem. -/
theorem antitone_step {A : C} (F : DecreasingFiltration A) : Antitone F.step := F.antitone

end DecreasingFiltration

namespace FilteredObject

/-- (blueprint: def-sp-filtration) Filtered objects and filtration-preserving maps
form the category `Fil(C)` (Stacks, Tag 0121). -/
instance : Category.{v} (FilteredObject C) where
  Hom := Hom
  id A := ⟨𝟙 A.obj, fun i => ⟨𝟙 _, by simp⟩⟩
  comp f g := ⟨f.hom ≫ g.hom, fun i => by
    obtain ⟨f_i, hf_i⟩ := f.preserves i
    obtain ⟨g_i, hg_i⟩ := g.preserves i
    exact ⟨f_i ≫ g_i, by rw [Category.assoc, hg_i, ← Category.assoc, hf_i,
      Category.assoc]⟩⟩
  id_comp := by
    intro A B f
    cases f
    congr 1
    simp
  comp_id := by
    intro A B f
    cases f
    congr 1
    simp
  assoc := by
    intro A B D E f g h
    cases f
    cases g
    cases h
    congr 1
    simp

end FilteredObject

namespace DecreasingFiltration

/-- (blueprint: def-sp-filtration) The filtration on an epimorphic quotient is the
image of each filtration step (Stacks, Tag 0121). -/
noncomputable abbrev quotient {A Y : C} (F : DecreasingFiltration A)
    (π : A ⟶ Y) [Epi π] : DecreasingFiltration Y := F.image π

/-- (blueprint: def-sp-filtration) The `n`-th graded piece is the quotient of
`Fⁿ A` by `Fⁿ⁺¹ A` (Stacks, Tag 0121; blueprint node). -/
noncomputable abbrev gradedPiece {A : C} (F : DecreasingFiltration A) (n : ℤ) : C :=
  F.gr n

end DecreasingFiltration

end CategoryTheory
