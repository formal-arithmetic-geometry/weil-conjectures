/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic

/-!
# Local smallness of `Loc(Dᵇc)` for the `ℓ`-adic coefficient rings

Blueprint `lemma-hypotheses-brown-representability--1`: for every admissible `Λ`, the category
`Loc(Dctf(X_proét, Λ))` is locally small. The morphisms of `Loc(Dᵇc(X)⟦Λ⟧)`, a full subcategory
of the derived category `D(X_proét, Λ_X)`, lie in `Type (u + 1)`, so the category is locally
`(u + 1)`-small (`locallySmall_localizingBoundedConstructible`, in the namespace
`AlgebraicGeometry.ProEtale.CondensedRing`).
For the `ℓ`-adic coefficient rings `𝒪̲_E, E̲, ℚ̲̄_ℓ` (for which `Dctf = Dᵇc`) this is stated by one
declaration each. For finite coefficient rings, see
`AlgebraicGeometry.ProEtale.locallySmall_derivedCategoryLocalizingFiniteTor`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The category `Loc(Dᵇc(X)⟦Λ⟧)` is locally `(u + 1)`-small, for every condensed coefficient
ring `Λ`: its morphisms are those of the derived category `D(X_proét, Λ_X)`, which lie in
`Type (u + 1)`. -/
theorem locallySmall_localizingBoundedConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : LocallySmall.{u + 1} (LocalizingBoundedConstructible Λ X) :=
  inferInstance

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

/-- Blueprint `lemma-hypotheses-brown-representability--1`: Local smallness, for `Λ = 𝒪̲_E`, `E`
a finite extension of `ℚ_ℓ` in `ℚ̄_ℓ` (for which `Dctf = Dᵇc`): the category
`Loc(Dᵇc(X)⟦𝒪_E⟧)` is locally small. -/
theorem locallySmall_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    LocallySmall.{u + 1}
      (LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X) :=
  locallySmall_localizingBoundedConstructible _ X

/-- Blueprint `lemma-hypotheses-brown-representability--1`: Local smallness, for `Λ = E̲`, `E` a
finite extension of `ℚ_ℓ` (for which `Dctf = Dᵇc`): the category `Loc(Dᵇc(X)⟦E⟧)` is locally
small. -/
theorem locallySmall_continuousMapRingObj (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    LocallySmall.{u + 1}
      (LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X) :=
  locallySmall_localizingBoundedConstructible _ X

/-- Blueprint `lemma-hypotheses-brown-representability--1`: Local smallness, for `Λ = ℚ̲̄_ℓ` (for
which `Dctf = Dᵇc`): the category `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)` is locally small. -/
theorem locallySmall_padicAlgClRingObj :
    LocallySmall.{u + 1} (LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  locallySmall_localizingBoundedConstructible _ X

end AlgebraicGeometry.ProEtale.CondensedRing
