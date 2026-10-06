/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Tensoring with an invertible object is an equivalence

If `T ⊗ T' ≅ 𝟙_ C` and `T' ⊗ T ≅ 𝟙_ C`, then `tensorRight T` is an equivalence of categories,
with inverse `tensorRight T'`.

## Main definitions

- `CategoryTheory.MonoidalCategory.tensorRightEquivalence`: the equivalence `- ⊗ T`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Tensoring with an invertible object is an equivalence.** If `T ⊗ T' ≅ 𝟙_ C` and
`T' ⊗ T ≅ 𝟙_ C`, then `tensorRight T : C ⥤ C` is an equivalence, with inverse
`tensorRight T'`. -/
noncomputable def tensorRightEquivalence (T T' : C) (e : T ⊗ T' ≅ 𝟙_ C) (e' : T' ⊗ T ≅ 𝟙_ C) :
    C ≌ C :=
  .mk (tensorRight T) (tensorRight T')
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e.symm ≪≫ tensorRightTensor T T')
    ((tensorRightTensor T' T).symm ≪≫ (tensoringRight C).mapIso e' ≪≫ rightUnitorNatIso C)

@[simp]
lemma tensorRightEquivalence_functor (T T' : C) (e : T ⊗ T' ≅ 𝟙_ C) (e' : T' ⊗ T ≅ 𝟙_ C) :
    (tensorRightEquivalence T T' e e').functor = tensorRight T :=
  rfl

end CategoryTheory.MonoidalCategory
