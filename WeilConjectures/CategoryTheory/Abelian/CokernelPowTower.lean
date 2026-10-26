/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The tower of reductions of an object modulo the powers of an integer

Let `C` be a preadditive category with cokernels, `A : C` and `ℓ : ℕ`. This file defines the
inverse system `n ↦ A/ℓⁿ = coker(ℓⁿ : A ⟶ A)` (`CategoryTheory.Limits.cokernelPowTower`), with the
reductions `A/ℓⁿ⁺¹ ⟶ A/ℓⁿ` as transition maps, and the cone of projections `A ⟶ A/ℓⁿ`
(`CategoryTheory.Limits.cokernelPowTowerCone`). The object `A` is `ℓ`-adically complete and
separated when this cone is a limit cone.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (A : C) (ℓ : ℕ)

lemma pow_succ_smul_comp_cokernel_π (n : ℕ) :
    (((ℓ ^ (n + 1) : ℕ) : ℤ) • 𝟙 A) ≫ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) = 0 := by
  rw [pow_succ', Nat.cast_mul, mul_smul, Preadditive.zsmul_comp, cokernel.condition, smul_zero]

/-- The reduction `A/ℓⁿ⁺¹ ⟶ A/ℓⁿ`. -/
noncomputable def cokernelPowTransition (n : ℕ) :
    cokernel (((ℓ ^ (n + 1) : ℕ) : ℤ) • 𝟙 A) ⟶ cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  cokernel.desc _ (cokernel.π _) (pow_succ_smul_comp_cokernel_π A ℓ n)

@[reassoc (attr := simp)]
lemma cokernel_π_cokernelPowTransition (n : ℕ) :
    cokernel.π _ ≫ cokernelPowTransition A ℓ n = cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  cokernel.π_desc _ _ _

/-- The inverse system `n ↦ A/ℓⁿ` of the reductions of `A` modulo the powers of `ℓ`. -/
noncomputable def cokernelPowTower : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A)) (cokernelPowTransition A ℓ)

lemma cokernelPowTower_obj (n : ℕ) :
    (cokernelPowTower A ℓ).obj (Opposite.op n) = cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  rfl

@[simp]
lemma cokernelPowTower_map_succ (n : ℕ) :
    (cokernelPowTower A ℓ).map (homOfLE (n.le_add_right 1)).op = cokernelPowTransition A ℓ n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The cone of the projections `A ⟶ A/ℓⁿ`. -/
noncomputable def cokernelPowTowerCone : Cone (cokernelPowTower A ℓ) where
  pt := A
  π := NatTrans.ofOpSequence (fun n ↦ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A)) (fun n ↦ by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      cokernelPowTower_map_succ]
    exact (cokernel_π_cokernelPowTransition A ℓ n).symm)

@[simp]
lemma cokernelPowTowerCone_π_app (n : ℕ) :
    (cokernelPowTowerCone A ℓ).π.app (Opposite.op n) = cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  rfl

end CategoryTheory.Limits
