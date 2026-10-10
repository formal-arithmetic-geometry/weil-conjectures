/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Precomposition on functor categories is braided

The functor category `C ⥤ E` is monoidal (resp. braided, symmetric) whenever `E` is, with all
the structure defined pointwise. Precomposition with a functor `F : C ⥤ D` is strong monoidal
by `CategoryTheory.Functor.Monoidal.whiskeringLeft`; here we record that it is moreover braided.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- Precomposition with a functor `F : C ⥤ D` is a braided functor `(D ⥤ E) ⥤ (C ⥤ E)`. -/
instance Functor.Braided.whiskeringLeft (E : Type*) [Category* E] [MonoidalCategory E]
    [BraidedCategory E] (F : C ⥤ D) : ((whiskeringLeft _ _ E).obj F).Braided where
  braided X Y := by
    ext c
    exact (Category.id_comp _).trans (Category.comp_id _).symm


/-- The constant functor `C ⥤ (J ⥤ C)` is monoidal for the pointwise monoidal structure on
`J ⥤ C`, with identity structure isomorphisms. -/
@[instance_reducible]
noncomputable def Functor.coreMonoidalConst (J E : Type*) [Category* J] [Category* E]
    [MonoidalCategory E] : (Functor.const J : E ⥤ J ⥤ E).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := NatIso.ofComponents (fun _ ↦ Iso.refl _)

noncomputable instance Functor.monoidalConst (J E : Type*) [Category* J] [Category* E]
    [MonoidalCategory E] : (Functor.const J : E ⥤ J ⥤ E).Monoidal :=
  (Functor.coreMonoidalConst J E).toMonoidal

@[simp]
lemma Functor.const_μ_app (J E : Type*) [Category* J] [Category* E] [MonoidalCategory E]
    (X Y : E) (j : J) : (Functor.LaxMonoidal.μ (Functor.const J) X Y).app j = 𝟙 _ :=
  rfl

@[simp]
lemma Functor.const_δ_app (J E : Type*) [Category* J] [Category* E] [MonoidalCategory E]
    (X Y : E) (j : J) : (Functor.OplaxMonoidal.δ (Functor.const J) X Y).app j = 𝟙 _ :=
  rfl

@[simp]
lemma Functor.const_ε_app (J E : Type*) [Category* J] [Category* E] [MonoidalCategory E]
    (j : J) : (Functor.LaxMonoidal.ε (Functor.const J : E ⥤ J ⥤ E)).app j = 𝟙 _ :=
  rfl

@[simp]
lemma Functor.const_η_app (J E : Type*) [Category* J] [Category* E] [MonoidalCategory E]
    (j : J) : (Functor.OplaxMonoidal.η (Functor.const J : E ⥤ J ⥤ E)).app j = 𝟙 _ :=
  rfl

end CategoryTheory
