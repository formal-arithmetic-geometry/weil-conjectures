/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralIdempotentComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import WeilConjectures.SixFunctors.ClosedImmersionStages

/-!
# The rational coefficient stage `Dᵇc(X, E)`

This file formalises *rationalization and coefficient-field extension*:
`Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ]` has the same objects as the integral category and morphisms
`Hom_{𝒪_E}(-, -) ⊗_{𝒪_E} E`; it is idempotent complete, so that the canonical functor to its Karoubi
envelope is an equivalence; `𝒪_E`-linear triangulated functors and natural transformations between
integral categories transport to the rational ones; every object of `Dᵇc(X, E)` is the
rationalization of an integral object (a lattice), and every morphism is `ϖ⁻ᴺ u` for an integral
morphism `u`.

## Modelling choices

* The integral category `Dᵇc(X, 𝒪_E)` is the full subcategory of the category
  `D_comp(X_ét, 𝒪_E)` of derived complete objects (`DerivedCategoryDerivedCompleteIntegral`) cut
  out by `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`. Its `Hom` groups
  are those of `D_comp(X_ét, 𝒪_E)`.
* The rational category `Dᵇc(X, E)` is the full subcategory
  `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational` of the rationalization
  `D_comp(X_ét, E)` of `D_comp(X_ét, 𝒪_E)` (`DerivedCategoryDerivedCompleteRational`, the
  Verdier quotient by the objects killed by a nonzero element of `𝒪_E`), consisting of the
  objects isomorphic to the image of an object of `Dᵇc(X, 𝒪_E)`. Since the functor induced on
  rationalizations by the fully faithful inclusion `Dᵇc(X, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` is fully
  faithful (`CategoryTheory.Rationalization.full_map`,
  `CategoryTheory.Rationalization.faithful_map`), this is the rationalization
  `Dᵇc(X, 𝒪_E)[1/ϖ]` of the integral category, and its `Hom` groups are those of the
  rationalization of `D_comp(X_ét, 𝒪_E)`.
* The descent of objects to lattices is then the definition of `boundedConstructibleRational`,
  and the description of the morphisms is the general computation of the `Hom` groups of a
  rationalization (`CategoryTheory.Rationalization.tensorHomEquiv`,
  `CategoryTheory.Rationalization.exists_eq_inv_pow_smul_map`), using that `𝒪_E` is a discrete
  valuation ring (`PadicAlgCl.isDiscreteValuationRing_integers`).
* Idempotent completeness belongs to another part of the blueprint and is only stated here
  (`AlgebraicGeometry.Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational`).
  The Karoubi envelope carries no triangulated structure in this repository, so the equivalence
  with the Karoubi envelope is stated as an equivalence of categories.

## Main results

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` : the morphisms
  of `Dᵇc(X, E)` between rationalizations of integral objects are `Hom_{𝒪_E} ⊗_{𝒪_E} E`.
- `AlgebraicGeometry.Etale.DerivedCategory.exists_iso_of_boundedConstructibleRational` : every
  object of `Dᵇc(X, E)` is the rationalization of an object of `Dᵇc(X, 𝒪_E)`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational_exists_eq_inv_pow_smul` :
  every morphism of `Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism `u`.
- `AlgebraicGeometry.Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational` :
  `Dᵇc(X, E)` is equivalent to its Karoubi envelope.
- `AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` : `𝒪_E`-linear triangulated
  functors and natural transformations transport to `E`-linear ones on rationalizations.
-/

@[expose] public section

universe w u

open CategoryTheory Limits TensorProduct

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- The ring of integers `𝒪_E` of a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` is a discrete
valuation ring. -/
instance isDiscreteValuationRing_integers : IsDiscreteValuationRing (integers l E) where
  not_a_field' := maximalIdeal_integers_ne_bot l E

/-- The universe `u + 1` copy `Shrink 𝒪_E` of the ring of integers of a finite extension `E` of
`ℚ_ℓ` inside `ℚ̄_ℓ` is a discrete valuation ring. -/
instance isDiscreteValuationRing_shrink [Small.{u + 1} E] :
    IsDiscreteValuationRing (Shrink.{u + 1} (integers l E)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (shrinkRingEquiv.{w, u} l E)

end PadicAlgCl

namespace AlgebraicGeometry

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

namespace Etale.DerivedCategory

variable (X : Scheme.{u})

end Etale.DerivedCategory

end AlgebraicGeometry
