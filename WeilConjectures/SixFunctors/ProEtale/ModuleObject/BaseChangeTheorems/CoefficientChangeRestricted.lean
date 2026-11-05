/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.PadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.PadicSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.ResidueField

/-!

# Coefficient change for restricted base change maps

For a commutative square `sq : g' ≫ p' = p ≫ g` and a morphism `i : Z ⟶ Y'`, consider the
*restricted base change map* `Li^* (Lg^* Rp_* K ⟶ Rp'_* Lg'^* K)`, the base change map followed by
the pullback along `i` (for nearby cycles: the base change of `Rj_*` restricted to the special
fibre). This file shows that it is compatible with the change of coefficients
`𝔽_E ⟵ 𝒪_E ⟶ E ⟶ ℚ̄_ℓ`:

* `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app`:
  extension of scalars along any `a : Λ ⟶ Λ'` carries the restricted base change map at `K` to
  the one at `T K`, if the pushforwards commute with `T` at `K` and `Lg'^* K`;
* `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`
  (derived Nakayama): with `𝒪_E`-coefficients, the restricted base change map at a derived
  complete bounded below `K` is invertible if it is invertible with `𝔽_E`-coefficients at
  `𝔽_E ⊗ᴸ K`;
* `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers` and
  `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`: the
  invertibility passes from `𝒪_E` to `E` to `ℚ̄_ℓ` by flat extension of scalars.

These are proved in the files of the directory `CoefficientChangeRestricted`, one per coefficient
change; this file combines them along an integral model
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
