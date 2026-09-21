/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.EditFromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives

-- Ported from the `WeilConjectures` module of the same name, with
-- `DerivedCategory` replaced by `DerivedCategory'` and every declaration primed.

/-!
## Every Grothendieck abelian category has K-injective resolutions
-/

@[expose] public section

namespace CategoryTheory.Abelian

/-- Every Grothendieck abelian category has K-injective resolutions: any cochain
complex admits a monomorphic quasi-isomorphism into a K-injective complex. This is a
theorem of Alonso Tarrío–Jeremías López–Souto Salorio and Serpé. -/
instance hasKInjectiveResolutions_of_isGrothendieckAbelian'
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasKInjectiveResolutions C :=
  sorry

end CategoryTheory.Abelian
