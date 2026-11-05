/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalization
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# The rationalization formula for `ℤ_ℓ,X`

The rationalization comparison
`κ : ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`
(`AlgebraicGeometry.ProEtale.rationalizationComparison`) is an isomorphism for `M = ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.isIso_rationalizationComparison_app_regular`). Identifying
`ℚ̄_ℓ ⊗ ℤ_ℓ,X ≅ ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsRegularIso`), under
which the unit is the inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsUnitAb_regular_comp`), the comparison sends
`g` in the `n`-th copy of the summand `b` to `b ℓ⁻ⁿ g`, and it is the composite of

* `colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯) ≅ ℚ_ℓ,X`, `g ↦ ℓ⁻ⁿ g`
  (`AlgebraicGeometry.ProEtale.isColimitPadicAbSheafCocone`): on sections the presheaf colimit
  is the group of the functions `ℓ⁻ⁿ g`, which are locally all continuous functions to `ℚ_ℓ`,
  a continuous function on an affine (hence compact) open being bounded
  (`PadicAlgCl.exists_padicInt_eq_pow_mul`);
* `⨁_{b ∈ B} ℚ_ℓ,X ≅ ℚ̄_ℓ,X`, `(q_b) ↦ ∑ b q_b`
  (`AlgebraicGeometry.ProEtale.isColimitAdicAbSheafCocone`): on sections the map from the
  presheaf direct sum is injective, `B` being linearly independent, and locally surjective, a
  locally finite function being near every point a finite combination of elements of `B` with
  continuous coefficients (`AlgebraicGeometry.ProEtale.exists_finset_sum_padicAlgClBasisIndex`).

Both are instances of `CategoryTheory.Sheaf.isColimitOfW`: a cocone of sheaves is a colimit
cocone if it receives a locally bijective map from a colimit cocone of the underlying presheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [HasWeakSheafify J A] {K : Type*} [Category* K]

end CategoryTheory.Sheaf

namespace AddCommGrpCat

universe v

section DirectSum

variable {B : Type} [DecidableEq B] (G : Discrete B ⥤ AddCommGrpCat.{v})

end DirectSum

end AddCommGrpCat

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-! ### `ℚ_ℓ,X = colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯)` -/

section PadicSheaf

end PadicSheaf

/-! ### `ℚ̄_ℓ,X = ⨁_{b ∈ B} ℚ_ℓ,X` -/

section PadicAlgClSheaf

attribute [local instance] padicAlgClBasisIndexDecidableEq

end PadicAlgClSheaf

/-! ### The rationalization formula for `ℤ_ℓ,X` -/

section Regular

end Regular

end AlgebraicGeometry.ProEtale
