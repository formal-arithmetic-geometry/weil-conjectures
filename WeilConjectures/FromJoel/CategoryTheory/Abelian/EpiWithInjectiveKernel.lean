/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel
public import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# Monomorphisms with a projective cokernel

Supplement to `Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.32.0`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category C] [Abelian C]

namespace Abelian

/-- The class of morphisms in an abelian category that are monomorphisms
and have a projective cokernel. -/
def monoWithProjectiveCokernel : MorphismProperty C :=
  fun _ _ f => Mono f ∧ Projective (cokernel f)

set_option backward.isDefEq.respectTransparency false in
lemma monoWithProjectiveCokernel_eq_unop :
    monoWithProjectiveCokernel (C := C) =
      epiWithInjectiveKernel.unop := by
  ext X Y f
  dsimp [monoWithProjectiveCokernel, epiWithInjectiveKernel]
  apply and_congr (by simp)
  rw [Injective.projective_iff_injective_op, Injective.iso_iff (kernelOpOp f).symm]

instance : (monoWithProjectiveCokernel : MorphismProperty C).IsMultiplicative := by
  rw [monoWithProjectiveCokernel_eq_unop]
  infer_instance

instance : (monoWithProjectiveCokernel : MorphismProperty C).IsStableUnderRetracts := by
  rw [monoWithProjectiveCokernel_eq_unop]
  infer_instance

lemma monoWithProjectiveCokernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    monoWithProjectiveCokernel f ↔ Projective Y := by
  simp only [monoWithProjectiveCokernel, hX.mono f, true_and]
  exact Projective.iso_iff
    { hom := cokernel.desc _ (𝟙 Y) (hX.eq_of_src _ _)
      inv := cokernel.π f }

end Abelian

end CategoryTheory
