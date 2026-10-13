/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula

/-!
# The projection formula for a bounded second argument

Let `Λ` be a finite ring, `g : Z ⟶ Y` a proper morphism and `j : U ⟶ Z` an open immersion. For
`K` in `Dᵇctf(U_proét, Λ)` and `L` a bounded complex of étale origin on `Y` (not necessarily of
finite Tor amplitude), the projection map `Rg_*(j_! K) ⊗ᴸ L ⟶ Rg_*(j_! K ⊗ᴸ Lg^* L)` is an
isomorphism. As in `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_comparison`
this is the étale projection formula transported along `ν^*`; the boundedness of
`j_! K ⊗ᴸ Lg^* L` now comes from the finite Tor amplitude of `K` rather than of `L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The projection formula for a bounded second argument.** For a finite ring `Λ`, a proper
`g : Z ⟶ Y`, an open immersion `j : U ⟶ Z`, `K` in `Dᵇctf(U_proét, Λ)` and `L₀` a bounded complex
of étale sheaves on `Y`, the projection map `Rg_*(j_! K) ⊗ᴸ ν^* L₀ ⟶ Rg_*(j_! K ⊗ᴸ Lg^* ν^* L₀)` is
an isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_bounded {Y Z U : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] (j : U ⟶ Z) [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K)
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL₀ : _root_.DerivedCategory.TStructure.t.bounded L₀) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K)).app (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj L₀)) :=
  sorry

end AlgebraicGeometry.ProEtale
