/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Invertible transposes through mates

Three formal facts on adjunctions used to show that a transpose under an adjunction is
invertible.

* `CategoryTheory.Adjunction.homEquiv_symm_map_comp_app`: the transpose of `G f ≫ β_Y` along
  `L₂ ⊣ R₂`, for a square `β : R₁ ⋙ G ⟶ H ⋙ R₂`, is the mate of `β` followed by `H` of the
  transpose of `f` along `L₁ ⊣ R₁`.
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_of_unit_comp`: if `R₃ ≅ R₂ ⋙ R₁` and
  `t : L₁ M ⟶ R₂ (L₃ M)` is compatible with the units, then the transpose of `t` along
  `L₂ ⊣ R₂` is invertible: it is a component of the comparison `L₁ ⋙ L₂ ≅ L₃` of left adjoints.
* `CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv`: when all four sides of a square are
  left adjoints, a square of right adjoints has invertible left mate as soon as its other mate
  is invertible (iterated mates are conjugates).

Source: Stacks Project, Tag 0GLL (adjunctions, mates and conjugates; Mac Lane, IV.7).
-/

@[expose] public section

namespace CategoryTheory

open Category

section Transpose

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

end Transpose

section LeftAdjointComparison

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : A ⥤ C} {R₃ : C ⥤ A}

end LeftAdjointComparison

section IteratedMate

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

end IteratedMate

end CategoryTheory
