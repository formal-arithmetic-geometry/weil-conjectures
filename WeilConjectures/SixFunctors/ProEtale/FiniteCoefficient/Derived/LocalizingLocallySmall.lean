/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing

/-!
# Local smallness of `Loc(Dctf)`, finite coefficients

Blueprint `lemma-hypotheses-brown-representability--1`: for every admissible `Λ`, the category
`Loc(Dctf(X_proét, Λ))` is locally small. For a finite coefficient ring `Λ`, the morphisms of
`Loc(Dctf(X, Λ))`, a full subcategory of `D(X_proét, Λ)`, lie in `Type (u + 1)`
(`AlgebraicGeometry.ProEtale.locallySmall_derivedCategoryLocalizingFiniteTor`). For the `ℓ`-adic
coefficient rings, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingLocallySmall`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Blueprint `lemma-hypotheses-brown-representability--1`: Local smallness, for a finite
coefficient ring `Λ`: the category `Loc(Dctf(X_proét, Λ))` is locally small, its morphisms being
those of the derived category `D(X_proét, Λ)`, which lie in `Type (u + 1)`. -/
theorem locallySmall_derivedCategoryLocalizingFiniteTor (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] (X : Scheme.{u}) : LocallySmall.{u + 1} (DerivedCategoryLocalizingFiniteTor Λ X) :=
  inferInstance

end AlgebraicGeometry.ProEtale
