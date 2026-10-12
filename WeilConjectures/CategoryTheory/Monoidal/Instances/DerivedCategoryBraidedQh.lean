/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The braiding of the derived tensor product on images of complexes

The braiding `DerivedCategory.braidedCategory C` of `DerivedCategory C` is characterised by the
commutativity of the square
```
Qh K ⊗ᴸ Qh M --β--> Qh M ⊗ᴸ Qh K
     |                  |
  Qh(K ⊗ M) --Qh β--> Qh(M ⊗ K)
```
whose vertical maps are the lax monoidal structure of `Qh`, the right braiding being the Koszul
braiding of the homotopy category (`DerivedCategory.braiding_hom_μ_Qh`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_braidedCategoryQh : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The braiding `DerivedCategory.braidedCategory C` on objects `Qh K`, `Qh M` is induced by the
Koszul braiding `K ⊗ M ≅ M ⊗ K` of the homotopy category, through the lax monoidal structure of
`Qh`. -/
@[reassoc]
lemma braiding_hom_μ_Qh (K M : HomotopyCategory C (ComplexShape.up ℤ)) :
    letI := braidedCategory C
    (β_ (Qh.obj K) (Qh.obj M)).hom ≫ μ Qh M K = μ Qh K M ≫ Qh.map (β_ K M).hom :=
  DerivedMonoidal.braiding_hom_μ _ _ K M

end DerivedCategory
