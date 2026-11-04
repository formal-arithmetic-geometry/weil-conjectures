/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Bidual

/-!
# The triangle identity of the biduality morphism of modules

The biduality morphism of `Hom_A(M, N)` followed by the dual of the biduality morphism of `M` is
the identity of `Hom_A(M, N)` (`CategoryTheory.Mod.bidual_comp_ihomMap_bidual`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The triangle identity of biduality: `Hom(M, N) ⟶ Hom(Hom(Hom(M, N), N), N) ⟶ Hom(M, N)`,
the biduality morphism of `Hom(M, N)` followed by the dual of the biduality morphism of `M`, is
the identity. -/
lemma bidual_comp_ihomMap_bidual (M N : Mod C A) :
    bidual ((ihom M).obj N) N ≫ (ihomMap (bidual M N)).app N = 𝟙 _ := by
  refine uncurryHom_injective ?_
  have h := uncurryHom_bidual M N
  rw [uncurryHom] at h
  rw [uncurryHom_comp_ihomMap, uncurryHom_bidual, BraidedCategory.braiding_naturality_right_assoc,
    h, SymmetricCategory.symmetry_assoc, uncurryHom, Mod.id_hom', id_whiskerRight,
    Category.id_comp]

end CategoryTheory.Mod
