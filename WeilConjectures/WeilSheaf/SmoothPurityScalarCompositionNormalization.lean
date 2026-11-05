/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer

/-! # Normalization of the ordinary coefficient-composition comparison -/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  {a : R ⟶ S} {b : S ⟶ T} {c : R ⟶ T} [IsMonHom a] [IsMonHom b] [IsMonHom c]

end Mod

end CategoryTheory
