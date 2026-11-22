/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # The canonical signed derived tensor symmetry

Source: Stacks Project, cohomology.tex, the symmetric monoidal structure on the derived
category.

## Main definitions

* `CategoryTheory.derivedTensorKoszulSymmetry` specializes the existing localization
  braiding to Qh and quasi-isomorphisms, caching the coefficient-category instances.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- The specified signed K-flat derived tensor braiding (a symmetry for symmetric
coefficients). Its data is the existing
localization braiding at Qh and quasi-isomorphisms, not a choice of braided structure.
Source: Stacks Project, cohomology.tex, the symmetric monoidal structure on the derived
category. -/
def derivedTensorKoszulSymmetry
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (K L : DerivedCategory C) : K ⊗ L ≅ L ⊗ K :=
  DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) K L

end CategoryTheory
