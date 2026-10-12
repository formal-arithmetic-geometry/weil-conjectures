/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula

/-!
# Derived scalar extension commutes with `Rf_!`

Let `S` be an algebra over a finite commutative ring `R` and write `Ψ = - ⊗ᴸ_R S` for the
derived extension of scalars `L(sheafExtendScalars (algebraMap R S) X)` of pro-étale sheaves.
For a morphism `f : X ⟶ Y` admitting a compactification `X ⟶[i] Z ⟶[g] Y`, the comparison map

`Ψ (Rf_! K) = Ψ (Rg_* i_! K) ⟶ Rg_* Ψ (i_! K) ≅ Rg_* i_! (Ψ K) = Rf_! (Ψ K)`

is built from the base change map of `Ψ` along `Rg_*`, the mate of the commutation
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso` of `Ψ` with `Lg^*`, and the
commutation of `Ψ` with the exact extension by zero `i_!`. It is an isomorphism on bounded
constructible complexes of finite Tor amplitude (blueprint `thm-trf-finite-coefficient-map`):
restricted back to `R`, the base change map is the projection map
`Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ S_Z)` for the constant sheaf `S_Y`, an isomorphism by the projection
formula.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekExtendScalarsIso`: `Ψ ∘ j_! ≅ j_! ∘ Ψ` for
  an open immersion `j`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarExtendScalarsMap`: the base change map
  `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app`: it is an
  isomorphism for proper `g`, at `M = i_! K` with `K` bounded constructible of finite Tor
  amplitude.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekExtendScalarsMap`: the comparison map
  `Ψ (Rf_! K) ⟶ Rf_! (Ψ K)`, and
  `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerShriekExtendScalarsMap_app`: it is an
  isomorphism on `Dᵇctf(X, R)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Derived scalar extension commutes with the extension by zero along an open immersion `j`:
`Ψ (j_! K) ≅ j_! (Ψ K)`. -/
noncomputable def openImmersionLowerShriekExtendScalarsIso :
    D((j)_!open[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) X) ≅
      L(sheafExtendScalars (algebraMap R S) U) ⋙ D((j)_!open[ModuleCat.{u + 1} S]) :=
  sorry

end OpenImmersion

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

section LowerShriek

variable [IsNoetherianRing R] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The comparison map `Ψ (Rf_! K) ⟶ Rf_! (Ψ K)` for a morphism `f` with chosen
compactification `X ⟶[i] Z ⟶[g] Y`: the base change map `Ψ (Rg_* i_! K) ⟶ Rg_* Ψ (i_! K)`
followed by `Rg_*` of `Ψ (i_! K) ≅ i_! (Ψ K)`. -/
noncomputable def rightDerivedLowerShriekExtendScalarsMap :
    R(f)_![ModuleCat.{u + 1} R] ⋙ L(sheafExtendScalars (algebraMap R S) Y) ⟶
      L(sheafExtendScalars (algebraMap R S) X) ⋙ R(f)_![ModuleCat.{u + 1} S] :=
  Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open[ModuleCat.{u + 1} R])
      (rightDerivedLowerStarExtendScalarsMap R S (HasCompactification.compactification f).g) ≫
    Functor.whiskerRight
      (openImmersionLowerShriekExtendScalarsIso R S (HasCompactification.compactification f).i).hom
      R(((HasCompactification.compactification f).g)_*[ModuleCat.{u + 1} S])

/-- **Derived scalar extension commutes with `Rf_!`** (blueprint
`thm-trf-finite-coefficient-map`): for a finite ring `R`, the comparison map
`Ψ (Rf_! K) ⟶ Rf_! (Ψ K)` is an isomorphism for `K` bounded constructible of finite Tor
amplitude. -/
theorem isIso_rightDerivedLowerShriekExtendScalarsMap_app [Finite R]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) :
    IsIso ((rightDerivedLowerShriekExtendScalarsMap R S f).app K) := by
  have := (HasCompactification.compactification f).isOpenImmersion
  have := (HasCompactification.compactification f).isProper
  have := isIso_rightDerivedLowerStarExtendScalarsMap_app R S
    (HasCompactification.compactification f).g (HasCompactification.compactification f).i hK
  simp only [rightDerivedLowerShriekExtendScalarsMap, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end LowerShriek

end AlgebraicGeometry.ProEtale
