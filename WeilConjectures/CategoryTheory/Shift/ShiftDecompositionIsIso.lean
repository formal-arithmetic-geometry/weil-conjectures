/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Shift.ShiftDecomposition

/-!

# Natural transformations invertible on finite direct sums of shifts

A natural transformation `τ : F ⟶ G` between additive functors is invertible at a finite direct sum
`P = ⨁ⱼ E⟦nⱼ⟧` of shifts of `E` as soon as it is invertible at the summands
(`CategoryTheory.ShiftDecomposition.isIso_app`), and, if `τ` commutes with the shifts, as soon as
it is invertible at `E` (`CategoryTheory.ShiftDecomposition.isIso_app_of_commShift`).

-/

@[expose] public section

namespace CategoryTheory.ShiftDecomposition

variable {C D : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Category D] [Preadditive D] {F G : C ⥤ D}
  [F.Additive] [G.Additive]

end CategoryTheory.ShiftDecomposition
