/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula

/-!
# Derived scalar extension commutes with `Rg_*` for proper `g`

Let `R` be a finite commutative ring and `S` an `R`-algebra. The base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension `Ψ = - ⊗ᴸ_R S` along the derived direct
image is the mate of the commutation of `Ψ` with `Lg^*`. For proper `g` it is an isomorphism at
`M = j_! K` with `K` bounded constructible of finite Tor amplitude on an open `j : U ⟶ Z`:
restricted back to `R`, it is the projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ Lg^* S_Y)` for the
constant sheaf `S_Y`, an isomorphism by the projection formula
(blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section LowerStar

variable [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension along the derived
direct image: the mate of the commutation `Lg^* ∘ Ψ ≅ Ψ ∘ Lg^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`). -/
noncomputable def rightDerivedLowerStarExtendScalarsMap :
    R((g)_*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Y) ⟶
      L(sheafExtendScalars (algebraMap R S) Z) ⋙ R((g)_*[ModuleCat.{u + 1} S]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedUpperStarExtendScalarsIso R S g).hom

/-- **Derived scalar extension commutes with `Rg_*` for proper `g`.** Let `R` be a finite ring
and `g : Z ⟶ Y` proper. For a complex `K` on an open subscheme `j : U ⟶ Z` that is bounded
constructible of finite Tor amplitude, the base change map `Ψ (Rg_* j_! K) ⟶ Rg_* Ψ (j_! K)` is an
isomorphism. Restricted to `R`, it is the projection map `Rg_* (j_! K) ⊗ᴸ S_Y ⟶ Rg_* (j_! K ⊗ᴸ S_Z)`
for the constant sheaf `S_Y`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app [Finite R] [IsProper g] {U : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) U K) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app
      (D((j)_!open[ModuleCat.{u + 1} R]).obj K)) :=
  sorry

end LowerStar

end AlgebraicGeometry.ProEtale
