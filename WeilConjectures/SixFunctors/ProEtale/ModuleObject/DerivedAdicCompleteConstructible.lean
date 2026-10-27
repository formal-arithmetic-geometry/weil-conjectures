/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicComplete
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama

/-!

# Bounded constructible integral complexes are derived complete

On a noetherian scheme `X`, a bounded constructible complex of `𝒪_{E,X}`-modules is derived
`ℓ`-adically complete (`ProEtale.isDerivedAdicComplete_of_boundedConstructible`): the derived
limit of the tower `⋯ --ℓ--> K --ℓ--> K` vanishes (`CategoryTheory.IsDerivedAdicComplete`). This
is the completeness half of the implication (1) ⇒ (2) of blueprint `sk-prop-integral-criterion`
(section `sec-proetale-coefficients`); the other half, that the first derived reduction is
bounded constructible, is `ProEtale.boundedConstructible_derivedReduction_obj`.

The derived category of module objects has countable products, since countable products of
module objects are exact (`ProEtale.CondensedRing.countableAB4Star_mod`,
`CategoryTheory.derivedCategory_hasCountableProducts`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]

/-- The derived category of module objects over a condensed coefficient ring on `X_proét` has
countable products: countable products of module objects are exact. -/
instance hasCountableProducts_derivedCategory_mod :
    HasCountableProducts (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  derivedCategory_hasCountableProducts _

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- **Bounded constructible integral complexes are derived complete** (blueprint
`sk-prop-integral-criterion`, section `sec-proetale-coefficients`, implication (1) ⇒ (2), the
completeness of `K`): on a noetherian scheme `X`, a bounded constructible complex `K` of
`𝒪_{E,X}`-modules is derived complete. Completeness is stated here for `ℓ ∈ 𝔪_E`, as the
vanishing of `R lim (⋯ --ℓ--> K --ℓ--> K)` (`CategoryTheory.IsDerivedAdicComplete`); since
`𝔪_E^e ⊆ (ℓ) ⊆ 𝔪_E`, this is equivalent to completeness for `𝔪_E` (Stacks, Tags 091N, 091Q). -/
theorem isDerivedAdicComplete_of_boundedConstructible [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    IsDerivedAdicComplete (ℓ : ℤ) K :=
  sorry

end AlgebraicGeometry.ProEtale
