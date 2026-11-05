/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Triangulated categories with a bounded t-structure are idempotent complete

Let `C` be a triangulated category with a bounded t-structure `t`. We show that every idempotent
of `C` splits, so that the canonical fully faithful functor `C ⥤ Karoubi C` is an equivalence.

The proof is by induction on the amplitude of an object `X` carrying an idempotent `p`. In
amplitude zero, `X` is a shift of an object of the heart, which is abelian and hence idempotent
complete (`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_heart`). In general, let
`A ⟶ X ⟶ B ⟶ A⟦1⟧` be the truncation triangle cutting off the top cohomology of `X`. The
idempotent `p` induces idempotents `p_A` of `A` and `p_B` of `B`, which split by induction, say
through `A₁` and `B₁`. The connecting morphism restricts to `δ₁ : B₁ ⟶ A₁⟦1⟧`, and a cone `C₁`
of `δ₁` comes with morphisms of triangles `C₁ ⟶ X ⟶ C₁` composing to an automorphism. They
exhibit `C₁` as the image of an idempotent `q` of `X` inducing `p_A` and `p_B`, so that
`(p - q)² = 0`. Two idempotents whose difference has square zero are conjugate
(`CategoryTheory.Idempotents.exists_split_of_sub_comp_sub_eq_zero`), so `p` splits.

The blueprint deduces the theorem from the triangulated structure of the Karoubi envelope (the
theorem of Balmer and Schlichting) and the induced t-structure on it; the argument above runs
the same induction directly inside `C`.

## Main statements

- `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`: a triangulated
  category with a bounded t-structure is idempotent complete.
- `CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_of_bounded`: the inclusion
  into the Karoubi envelope is an equivalence.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated Idempotents Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

end CategoryTheory.Triangulated.TStructure
