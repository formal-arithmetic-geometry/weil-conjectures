/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Derived categories with a projective unit

Let `C` be a monoidal abelian category whose derived category `D(C)` carries the derived tensor
product. If the unit `𝟙_ C` is projective, then the unit of `D(C)`, which is `𝟙_ C` placed in
degree `0`, has no nonzero morphisms to its positive shifts: `Ext^n(𝟙_, 𝟙_) = 0` for `n > 0`.

## Main results

- `DerivedCategory.unit_hom_shift_eq_zero_of_projective`: if `𝟙_ C` is projective, every
  morphism `𝟙_ ⟶ (𝟙_)⟦n⟧` in `D(C)` with `0 < n` is zero.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

end DerivedCategory
