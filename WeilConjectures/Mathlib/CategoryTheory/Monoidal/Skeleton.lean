/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensor powers and the monoid homomorphism induced on skeleta

The class of a tensor power `X ^⊗ n` in the skeleton of a monoidal category is the `n`-th power
of the class of `X`.

A monoidal functor `F : C ⥤ D` induces a monoid homomorphism
`CategoryTheory.Skeleton.monoidHom F : Skeleton C →* Skeleton D`. We record that this
construction only depends on `F` up to isomorphism, and that it is compatible with the
identity functor and with the composition of functors.

## Main results

- `CategoryTheory.Skeleton.toSkeleton_tensorPow`
- `CategoryTheory.Skeleton.monoidHom_congr`
- `CategoryTheory.Skeleton.monoidHom_id`
- `CategoryTheory.Skeleton.monoidHom_comp`

-/

@[expose] public section

namespace CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

open MonoidalCategory in
@[simp]
lemma Skeleton.toSkeleton_tensorPow (X : C) : ∀ n : ℕ, toSkeleton (X ^⊗ n) = toSkeleton X ^ n
  | 0 => Skeleton.one_eq.symm
  | n + 1 => by
    rw [tensorPow_succ, Skeleton.toSkeleton_tensorObj, Skeleton.toSkeleton_tensorPow X n, pow_succ]

@[simp]
lemma Skeleton.monoidHom_toSkeleton (F : C ⥤ D) [F.Monoidal] (X : C) :
    Skeleton.monoidHom F (toSkeleton X) = toSkeleton (F.obj X) :=
  F.mapSkeleton_obj_toSkeleton X

/-- The monoid homomorphism induced on the skeleta by a monoidal functor only depends on the
functor up to isomorphism. -/
lemma Skeleton.monoidHom_congr {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G) :
    Skeleton.monoidHom F = Skeleton.monoidHom G := by
  ext x
  rw [← toSkeleton_fromSkeleton_obj x, monoidHom_toSkeleton, monoidHom_toSkeleton]
  exact congr_toSkeleton_of_iso (e.app _)

variable (C) in
/-- The identity functor induces the identity of the skeleton. -/
lemma Skeleton.monoidHom_id : Skeleton.monoidHom (𝟭 C) = MonoidHom.id (Skeleton C) := by
  ext x
  rw [← toSkeleton_fromSkeleton_obj x, monoidHom_toSkeleton]
  rfl

/-- The monoid homomorphism induced on the skeleta by a composition of monoidal functors is
the composition of the induced monoid homomorphisms. -/
lemma Skeleton.monoidHom_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    Skeleton.monoidHom (F ⋙ G) = (Skeleton.monoidHom G).comp (Skeleton.monoidHom F) := by
  ext x
  rw [← toSkeleton_fromSkeleton_obj x, monoidHom_toSkeleton]
  rw [MonoidHom.comp_apply, monoidHom_toSkeleton, monoidHom_toSkeleton]
  rfl

end CategoryTheory
