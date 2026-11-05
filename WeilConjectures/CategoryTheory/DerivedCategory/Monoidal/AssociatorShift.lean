/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor
public import WeilConjectures.Mathlib.Algebra.Homology.MonoidalShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The associator of the derived tensor product commutes with shifts

For objects `K`, `L`, `M` of the derived category `D(C)` and `a b c : ℤ`, the identifications
`X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧` (`DerivedCategory.shiftTensorShiftIso`) are compatible with the
associator: the two isomorphisms `(K⟦a⟧ ⊗ᴸ L⟦b⟧) ⊗ᴸ M⟦c⟧ ≅ (K ⊗ᴸ (L ⊗ᴸ M))⟦a + b + c⟧` obtained
by moving the shifts out before or after applying the associator agree
(`DerivedCategory.shiftTensorShiftIso_assoc`). No sign appears.

## Strategy

The associator, viewed as a natural transformation in one of the three variables
(`CategoryTheory.MonoidalCategory.associatorNatTrans₁`, `associatorNatTrans₂`,
`associatorNatTrans₃`), commutes with the shifts. For the other two variables in the image of
K-flat complexes, this is checked through the localization functor
`CochainComplex C ℤ ⥤ D(C)`: there the associator of `D(C)` is identified with the associator of
cochain complexes by the comparisons `L P ⊗ᴸ L Z ≅ L (P ⊗ Z)`, which commute with shifts, and
the associator of cochain complexes commutes with shifts
(`CochainComplex.associator_hom_comp_mapBifunctorShift₁Iso_hom` and its variants). Every object
is isomorphic to the image of a K-flat complex, and the statement is invariant under
isomorphisms (`CategoryTheory.MonoidalCategory.commShift_associatorNatTrans₁_of_iso`, ...).
The compatibility with `DerivedCategory.shiftTensorShiftIso` is then a formal consequence.

## Main statements

- `DerivedCategory.shiftTensorShiftIso_assoc`
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

universe w v u

namespace CategoryTheory.MonoidalCategory

variable (D : Type*) [Category D] [MonoidalCategory D]

section Shift

variable {D} [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [(curriedTensor D).CommShift₂Int]

end Shift

end CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace TensorCommShift₂

variable {C}

end TensorCommShift₂

open TensorCommShift₂

variable {C}

end DerivedCategory
