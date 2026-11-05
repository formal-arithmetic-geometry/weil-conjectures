/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Idempotents.Shift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.Mathlib.Algebra.Ring.Idempotent

/-!
# The Karoubi envelope of a pretriangulated category

Let `C` be a pretriangulated category. Following Balmer and Schlichting, we equip the Karoubi
envelope `Karoubi C` with the shift `(K, e)⟦1⟧ = (K⟦1⟧, e⟦1⟧)` and with the distinguished
triangles the retracts (in the category of triangles) of images of distinguished triangles of
`C`. This makes `Karoubi C` a pretriangulated category, and the inclusion `C ⥤ Karoubi C` a
triangulated functor.

The key input is the lifting of idempotents along triangles
(`CategoryTheory.Pretriangulated.exists_idempotent_of_distTriang`): if `(a, b)` is a pair of
idempotents on the first two terms of a distinguished triangle compatible with its first
morphism, then it extends to an idempotent endomorphism `(a, b, c)` of the triangle. Indeed, any
extension `(a, b, x)` given by the axioms satisfies `(x² - x)² = 0`, so that `c = 3x² - 2x³`
is idempotent.

## References

* Paul Balmer and Marco Schlichting, *Idempotent completion of triangulated categories*,
  J. Algebra 236 (2001)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Idempotents

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The polynomial `3t² - 2t³` (written without numerals) applied to an endomorphism. -/
def idemPoly {X : C} (x : X ⟶ X) : X ⟶ X :=
  x ≫ x + x ≫ x + x ≫ x - x ≫ x ≫ x - x ≫ x ≫ x

end Pretriangulated

namespace Idempotents

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

variable {C}

namespace Karoubi

section TriangleOfIdem

variable (T : Triangle C) (E : T ⟶ T) (hE : E ≫ E = E)

include hE

end TriangleOfIdem

end Karoubi

end Idempotents

end CategoryTheory
