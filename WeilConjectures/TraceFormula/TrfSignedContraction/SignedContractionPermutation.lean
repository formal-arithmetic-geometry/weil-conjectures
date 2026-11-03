/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # The signed permutation in the exchange contraction

Source: the latest diagonal-pairing proof, Step 3(c), comparing the two four-factor
permutations (blueprint: lem-trf-signed-contraction-permutation).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe v u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace WeilConjectures.TrfSignedContraction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (A B C' D : C)

private def moveThird : (A ⊗ B) ⊗ (C' ⊗ D) ⟶ (C' ⊗ A) ⊗ (B ⊗ D) :=
  (α_ (A ⊗ B) C' D).inv ≫ ((α_ A B C').hom ▷ D) ≫
    ((A ◁ (β_ B C').hom) ▷ D) ≫ ((α_ A C' B).inv ▷ D) ≫
    (((β_ A C').hom ▷ B) ▷ D) ≫ (α_ (C' ⊗ A) B D).hom

private theorem moveThird_tensor : moveThird A B C' D =
    tensorμ A B C' D ≫ ((β_ A C').hom ⊗ₘ 𝟙 (B ⊗ D)) := by
  dsimp only [moveThird, tensorμ]
  monoidal

/-- Moving the third factor, after the second-pair swap and before the block swap,
is the cyclic permutation moving the first factor to the end.
Source: diagonal-pairing proof Step 3(c), the displayed sign calculation
(blueprint: lem-trf-signed-contraction-permutation).
Proof: express the move as middle-four interchange followed by the first-pair swap.
Naturality moves that swap through the final block braiding. The source-library
middle-four braiding equation exchanges the two input pairs. The two swaps on the
second pair cancel by symmetry. Expand the remaining interchange and hexagon;
monoidal coherence identifies the associators. This proves equality of the actual
maps, and hence includes the Koszul signs in a derived category. -/
theorem exchange_signed_permutation :
    (𝟙 (A ⊗ B) ⊗ₘ (β_ C' D).hom) ≫
      ((α_ (A ⊗ B) D C').inv ≫ ((α_ A B D).hom ▷ C') ≫
      ((A ◁ (β_ B D).hom) ▷ C') ≫ ((α_ A D B).inv ▷ C') ≫
      (((β_ A D).hom ▷ B) ▷ C') ≫ (α_ (D ⊗ A) B C').hom) ≫
        (β_ (D ⊗ A) (B ⊗ C')).hom =
      (α_ A B (C' ⊗ D)).hom ≫ (β_ A (B ⊗ (C' ⊗ D))).hom ≫
        (α_ B (C' ⊗ D) A).hom ≫ (B ◁ (α_ C' D A).hom) ≫
        (α_ B C' (D ⊗ A)).inv := by
  change (𝟙 (A ⊗ B) ⊗ₘ (β_ C' D).hom) ≫ moveThird A B D C' ≫
    (β_ (D ⊗ A) (B ⊗ C')).hom = _
  rw [moveThird_tensor]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality]
  rw [SymmetricCategory.tensorμ_braiding_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, SymmetricCategory.symmetry]
  simp only [tensorμ, BraidedCategory.braiding_tensor_right_hom]
  monoidal

end WeilConjectures.TrfSignedContraction
