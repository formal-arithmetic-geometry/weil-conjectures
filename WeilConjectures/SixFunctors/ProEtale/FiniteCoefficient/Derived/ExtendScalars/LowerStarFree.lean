/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableSingle
public import WeilConjectures.CategoryTheory.Monoidal.DualizableFree
public import WeilConjectures.NumberTheory.Padics.IntegersMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStarDualizable

/-!
# Derived extension of scalars along a finite free algebra commutes with `Rg_*`

Let `R` be a commutative ring and `S` an `R`-algebra which is finite free as an `R`-module. The
constant complex `S_Y` of `R`-modules on `Y_proét` is a finite direct sum of copies of the unit
`R_Y`, hence dualizable in `D(Y_proét, R)`. Therefore the base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension `Ψ = - ⊗ᴸ_R S` along the derived direct
image is an isomorphism for every morphism `g` and every `M`
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable`).
This applies to the common-stage scalar extension `𝒪_E → 𝒪_{E'}` of rings of integers of finite
extensions of `ℚ_ℓ`.

## Main results

- `AlgebraicGeometry.ProEtale.isDualizable_singleFunctor_constantSheaf_of_free`: the constant
  complex `M_X` of a finite free `R`-module `M` is dualizable in `D(X_proét, R)`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_free`: extension
  of scalars along a finite free algebra commutes with `Rg_*`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap`:
  the common-stage scalar extension `𝒪_E → 𝒪_{E'}` commutes with `Rg_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The constant complex `M_X` of a finite free `R`-module `M`, placed in degree `0`, is
dualizable in `D(X_proét, R)`: the constant sheaf functor is additive and sends `R` to the unit
sheaf, so that the constant sheaf `M_X` is dualizable
(`CategoryTheory.Functor.isDualizable_obj_of_free`). -/
theorem isDualizable_singleFunctor_constantSheaf_of_free {R : Type (u + 1)} [CommRing R]
    (X : Scheme.{u}) (M : ModuleCat.{u + 1} R) [Module.Free R M] [Module.Finite R M] :
    IsDualizable
      ((DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj M)) :=
  DerivedCategory.isDualizable_singleFunctor_obj
    ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).isDualizable_obj_of_free
      (isDualizable_unit.of_iso (Iso.refl _)) M)

/-- **Finite free extension of scalars commutes with `Rg_*`.** For an `R`-algebra `S` which is
finite free as an `R`-module and any morphism `g : Z ⟶ Y`, the base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension along the derived direct image of
pro-étale sheaves is an isomorphism for every `M ∈ D(Z_proét, R)`: the constant complex `S_Y` is
dualizable (`AlgebraicGeometry.ProEtale.isDualizable_singleFunctor_constantSheaf_of_free`). -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_free (R S : Type (u + 1)) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app M) :=
  isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable R S g
    ((isDualizable_singleFunctor_constantSheaf_of_free Y (ModuleCat.of R S)).of_iso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf _ _).mapIso
        (restrictScalarsAlgebraMapUnitIso R S).symm))) M

/-- **The common-stage scalar extension commutes with `Rg_*`.** For finite extensions `E ⊆ E'`
of `ℚ_ℓ` inside `ℚ̄_ℓ`, the base change map `(Rg_* M) ⊗ᴸ 𝒪_{E'} ⟶ Rg_* (M ⊗ᴸ 𝒪_{E'})` of
pro-étale sheaves is an isomorphism for every morphism `g : Z ⟶ Y` and every
`M ∈ D(Z_proét, 𝒪_E)`, `𝒪_{E'}` being a finite free `𝒪_E`-module. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_integersShrinkMap (l : ℕ) [Fact l.Prime]
    (E E' : Type) [Field E] [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)]
    [Algebra E E'] [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E']
    [IsScalarTower ℚ_[l] E' (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E]
    [Small.{u + 1} E'] {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))) :
    letI := (PadicAlgCl.integersShrinkMap.{0, u} l E E').toAlgebra
    IsIso ((rightDerivedLowerStarExtendScalarsMap (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (Shrink.{u + 1} (PadicAlgCl.integers l E')) g).app M) := by
  let := (PadicAlgCl.integersShrinkMap.{0, u} l E E').toAlgebra
  obtain ⟨n, b, -, -⟩ := PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap.{0, u} l E E'
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  exact isIso_rightDerivedLowerStarExtendScalarsMap_app_of_free _ _ g M

end AlgebraicGeometry.ProEtale
