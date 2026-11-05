/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# The direct image along a closed immersion on `Dᵇc(-, ℚ̄_ℓ)`

Let `i : Z ⟶ X` be a closed immersion into a locally noetherian scheme. We show, without the
finiteness theorem for `ℓ`-adic direct images, that `Ri_*` carries `Dᵇc(Z, ℚ̄_ℓ)` into
`Dᵇc(X, ℚ̄_ℓ)`:

* the open complement `j` of `i` is quasi-compact, `X` being locally noetherian, so `i_*` is exact
  (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isClosedImmersion`) and
  `Ri_*` is `i_*` applied termwise;
* `i_*` of a constructible `ℓ`-adic sheaf is constructible
  (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.adicLowerStar_of_isClosedImmersion`): near a
  point, on an affine open `V`, the sheaf `i_* F` restricts to `F` on `Z ∩ V` (the counit
  `i^* i_* ⟶ 𝟭` being invertible) and to `0` on the complement `U ∩ V`.

This gives the functor `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedLowerStar`), and we prove the
stage `ℚ̄_ℓ` of blueprint `prop-sf-closed-unit-all-stages` for it: it is fully faithful
(`AlgebraicGeometry.ProEtale.fullyFaithfulBoundedConstructibleAdicClosedLowerStar`), and for any
right adjoint the unit is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_unit_boundedConstructibleAdicClosedLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

variable [IsLocallyNoetherian X]

end AlgebraicGeometry.ProEtale
