/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The integral constructibility criterion

Blueprint `sk-prop-integral-criterion` (section `sec-proetale-coefficients`): on a noetherian
scheme `X`, a complex `K ∈ D(X_proét, 𝒪_E)` is bounded constructible if and only if it is derived
complete and its first derived reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` lies in `Dᵇc(X, 𝔽_E)`
(Bhatt–Scholze, Proposition 6.8.11; Stacks, Tag 09C7).

The implication (1) ⇒ (2) is `ProEtale.derivedCompleteIntegers_of_boundedConstructible` and
`ProEtale.boundedConstructible_derivedReduction_obj`. This file states the converse
(2) ⇒ (1), `ProEtale.boundedConstructible_of_derivedCompleteIntegers`.

## Sorried input

- `ProEtale.boundedConstructible_of_derivedCompleteIntegers`, the implication (2) ⇒ (1) of
  blueprint `sk-prop-integral-criterion` (section `sec-proetale-coefficients`), proved there
  through the bounds for the finite reductions (blueprint `sk-lem-integral-finite-levels`) and
  the Mittag-Leffler argument on a weakly contractible cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- Blueprint `sk-prop-integral-criterion` (section `sec-proetale-coefficients`), implication
(2) ⇒ (1): on a noetherian scheme `X`, a derived complete complex `K` of `𝒪_{E,X}`-modules whose
first derived reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` lies in `Dᵇc(X, 𝔽_E)` is bounded
constructible (Bhatt–Scholze, Proposition 6.8.11). -/
theorem boundedConstructible_of_derivedCompleteIntegers
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K :=
  sorry

end AlgebraicGeometry.ProEtale
