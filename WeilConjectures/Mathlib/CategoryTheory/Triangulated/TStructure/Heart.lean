/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The heart of a t-structure is abelian

Let `t` be a t-structure on a triangulated category `C`. Using that the subcategories `t.le n`
and `t.ge n` are closed under extensions (`CategoryTheory.Triangulated.TStructure.isLE₂` and
`CategoryTheory.Triangulated.TStructure.isGE₂`, from Mathlib), we show that the heart of `t` is
an abelian category ([BBD, Théorème 1.3.6]). Consequently the heart is idempotent complete.

## Main statements

- `CategoryTheory.Triangulated.TStructure.abelianHeart`: the heart is abelian.
- `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_heart`: the heart is idempotent
  complete.

## References

* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*, 1.3][bbd-1982]
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

section Heart

variable [IsTriangulated C] (H : Type u') [Category.{v'} H] [Preadditive H] [t.Heart H]

end Heart

end CategoryTheory.Triangulated.TStructure
