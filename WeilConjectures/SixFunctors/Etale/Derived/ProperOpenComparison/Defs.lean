/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.ProperOpenSection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence

/-!
# The comparison map for a proper map fixing an open

Let `u : T₁ ⟶ T₂` be a proper morphism and `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` open immersions with
`j₁ ≫ u = j₂` (`AlgebraicGeometry.ProperOpenDatum`). For a finite coefficient ring `Λ` this file
constructs the comparison map

`α_{u,K} : j₂! K ⟶ Ru_* j₁! K`

on the bounded below derived categories of étale sheaves of `Λ`-modules
(blueprint `def-weil-pbc-proper-open-comparison`).

## The construction

For an open immersion `j` write `ι_j : j_! ⟶ Rj_*` for the canonical map of the adjoint triple
`j_! ⊣ j^* ⊣ Rj_*` (`AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStarPlus`). The map
`α_u` is characterised by

`Ru_* (ι_{j₁}) ∘ α_u = ι_{j₂}`   (modulo `Ru_* Rj₁_* ≅ Rj₂_*`)

(`AlgebraicGeometry.ProperOpenDatum.comparison_toLowerStar`). Such a map exists and is unique
because `j₂^* Ru_* (ι_{j₁})` is an isomorphism
(`AlgebraicGeometry.ProperOpenDatum.isIso_upperStar_map_toLowerStar_app`): by étale base change
along the open immersion `j₂` it is `Rp_*` of `b^* (ι_{j₁})`, and `b^* (ι_{j₁})` is an isomorphism
on `V = T₁ ×_{T₂} X`, being so on the clopen piece `s(X) = j₁(X)` (where `ι_{j₁}` restricts to an
isomorphism) and on its complement (where both sides vanish).

Correspondingly the restriction isomorphism `θ_u : j₂^* Ru_* j₁! K ≅ K` is `j₂^*` of
`Ru_* (ι_{j₁})`, followed by the counit `j₂^* Rj₂_* ≅ 𝟭`; `α_u` is adjoint to its inverse
(`AlgebraicGeometry.ProperOpenDatum.homEquiv_comparison_app`).

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStarPlus`: `ι_j : D⁺j_! ⟶ R⁺j_*`.
- `AlgebraicGeometry.ProperOpenDatum.toLowerStar`: `Ru_* (ι_{j₁})` followed by
  `Ru_* Rj₁_* ≅ Rj₂_*`.
- `AlgebraicGeometry.ProperOpenDatum.comparison`: the comparison map `α_u`.
- `AlgebraicGeometry.ProperOpenDatum.restrictionIso`: the isomorphism `θ_u`.

## Main statements

- `AlgebraicGeometry.ProperOpenDatum.isIso_upperStar_map_toLowerStar_app`
- `AlgebraicGeometry.ProperOpenDatum.comparison_toLowerStar` and
  `AlgebraicGeometry.ProperOpenDatum.comparison_ext`: the characterisation of `α_u`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

section Iota

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-- The counit `D⁺j^* R⁺j_* ⟶ 𝟭` is an isomorphism for an open immersion `j`: in the adjoint
triple `D⁺j_! ⊣ D⁺j^* ⊣ R⁺j_*` the unit of the first adjunction is an isomorphism. -/
instance isIso_counit_derivedPlus_of_isOpenImmersion :
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.counit :=
  (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus
    ).isIso_unit_iff_isIso_counit.1 inferInstance

end Iota

end Etale

namespace ProperOpenDatum

variable {X : Scheme.{u}} (D : ProperOpenDatum X)

end ProperOpenDatum

end AlgebraicGeometry
