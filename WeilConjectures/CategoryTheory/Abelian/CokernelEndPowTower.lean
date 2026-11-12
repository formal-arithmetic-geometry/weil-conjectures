/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The tower of cokernels of the powers of an endomorphism

Let `C` be a category with zero morphisms and cokernels and `φ : A ⟶ A` an endomorphism. This
file sets up the inverse system `n ↦ A/φⁿ = coker(φⁿ)`
(`CategoryTheory.Limits.cokernelEndPowTower`), with the reductions `A/φⁿ⁺¹ ⟶ A/φⁿ` as
transition maps, and the cone of projections `A ⟶ A/φⁿ`
(`CategoryTheory.Limits.cokernelEndPowTowerCone`). For a module `M` over a ring and the
multiplication `φ` by an element `ϖ`, these are the reductions `M/ϖⁿM` of `M` and the object `A`
is `ϖ`-adically complete and separated when the cone is a limit cone.

For `φ = ℓ • 𝟙 A` with `ℓ : ℕ` this is the tower `CategoryTheory.Limits.cokernelPowTower A ℓ` of
`WeilConjectures.CategoryTheory.Abelian.CokernelPowTower`, which is indexed by the multiples
`ℓⁿ • 𝟙 A` rather than by the powers `φⁿ`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C] {A : C}
  (φ : End A)

lemma pow_succ_comp_cokernel_π_pow (n : ℕ) :
    (φ ^ (n + 1) : A ⟶ A) ≫ cokernel.π (φ ^ n : A ⟶ A) = 0 := by
  rw [pow_succ, End.mul_def, Category.assoc, cokernel.condition, Limits.comp_zero]

/-- The reduction `A/φⁿ⁺¹ ⟶ A/φⁿ`. -/
noncomputable def cokernelEndPowTransition (n : ℕ) :
    cokernel (φ ^ (n + 1) : A ⟶ A) ⟶ cokernel (φ ^ n : A ⟶ A) :=
  cokernel.desc _ (cokernel.π _) (pow_succ_comp_cokernel_π_pow φ n)

@[reassoc (attr := simp)]
lemma cokernel_π_cokernelEndPowTransition (n : ℕ) :
    cokernel.π _ ≫ cokernelEndPowTransition φ n = cokernel.π (φ ^ n : A ⟶ A) :=
  cokernel.π_desc _ _ _

/-- The inverse system `n ↦ A/φⁿ` of the reductions of `A` modulo the powers of `φ`. -/
noncomputable def cokernelEndPowTower : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ cokernel (φ ^ n : A ⟶ A)) (cokernelEndPowTransition φ)

lemma cokernelEndPowTower_obj (n : ℕ) :
    (cokernelEndPowTower φ).obj (Opposite.op n) = cokernel (φ ^ n : A ⟶ A) :=
  rfl

@[simp]
lemma cokernelEndPowTower_map_succ (n : ℕ) :
    (cokernelEndPowTower φ).map (homOfLE (n.le_add_right 1)).op = cokernelEndPowTransition φ n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The cone of the projections `A ⟶ A/φⁿ`. -/
noncomputable def cokernelEndPowTowerCone : Cone (cokernelEndPowTower φ) where
  pt := A
  π := NatTrans.ofOpSequence (fun n ↦ cokernel.π (φ ^ n : A ⟶ A)) (fun n ↦ by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      cokernelEndPowTower_map_succ]
    exact (cokernel_π_cokernelEndPowTransition φ n).symm)

@[simp]
lemma cokernelEndPowTowerCone_π_app (n : ℕ) :
    (cokernelEndPowTowerCone φ).π.app (Opposite.op n) = cokernel.π (φ ^ n : A ⟶ A) :=
  rfl

end CategoryTheory.Limits
