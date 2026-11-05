/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryBiproductPow
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapBiproduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldFiniteFree

/-!
# Derived extension followed by restriction of scalars along `E_X ⟶ F_X`

For finite subextensions `E ≤ F` of `ℚ̄_ℓ / ℚ_ℓ` and a scheme `X`, the coefficient ring `F_X` is
finite free of some rank `d` over `E_X`
(`ProEtale.CondensedRing.exists_comap_regular_iso_finiteFree`). Hence the derived extension of
scalars along `E_X ⟶ F_X` followed by the restriction of scalars is the biproduct power
`K ↦ Kᵈ` on the unbounded derived category of `E_X`-modules
(`ProEtale.CondensedRing.exists_extendScalars_comp_restrictScalars_iso_biproductPow`): extension
of scalars is exact, so its left derived functor is computed levelwise, and on module objects
`φ^* (F_X ⊗_{E_X} M) ≅ φ^* F_X ⊗_{E_X} M ≅ Mᵈ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

end AlgebraicGeometry.ProEtale.CondensedRing
