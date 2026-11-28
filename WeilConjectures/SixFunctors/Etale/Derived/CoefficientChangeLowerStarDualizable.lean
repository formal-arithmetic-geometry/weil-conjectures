/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStarFiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaConstant

/-!
# Derived extension of scalars along a dualizable algebra commutes with `Rf_*`

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings such that the constant complex `Λ'_Y` of
`Λ`-modules is dualizable in `D(Y_ét, Λ)`. Then for every morphism `f : X ⟶ Y` the base change
map `(Rf_* K) ⊗ᴸ_Λ Λ' ⟶ Rf_* (K ⊗ᴸ_Λ Λ')` is an isomorphism for every `K ∈ D(X_ét, Λ)`:
restricted back to `Λ`, it is the projection map `Rf_* K ⊗ᴸ Λ'_Y ⟶ Rf_* (K ⊗ᴸ Λ'_X)`, an
isomorphism at the dualizable object `Λ'_Y`.

## Main results

- `isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isDualizable`:
  the base change map along an `R`-algebra `S` with `S_Y` dualizable is an isomorphism.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable`:
  the same for a ring homomorphism `ρ : Λ →+* Λ'`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow`:
  the reduction `Λ ⟶ Λ/ϖⁿ` modulo a power of a nonzerodivisor `ϖ` commutes with `Rf_*`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_free`:
  extension of scalars along a finite free `Λ`-algebra `Λ'` commutes with `Rf_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

-- Use the monoidal structure of the derived tensor product of étale sheaves, see
-- `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Derived extension of scalars along a dualizable algebra commutes with `Rg_*`.** For an
`R`-algebra `S` such that the constant complex `S_Y` of `R`-modules is dualizable and any
morphism `g : Z ⟶ Y`, the base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)`, the mate of
`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`, is an isomorphism. -/
theorem isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isDualizable
    (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (hS : IsDualizable (constantSingle (ModuleCat.{u + 1} R) Y
      ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S)))))
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom).app M) := by
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)).app M).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) :=
    (NatTrans.isIso_app_iff_of_iso
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app M)
      (derivedSingleSheafRestrictScalarsUnitIso R S Y)).2
      (isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable _ g M hS)
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app M) :=
    Adjunction.isIso_mateEquiv_app_of_isIso_rightAdjointProjectionMap
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)
      (leftDerivedUpperStarDerivedSingleMap g (upperStarSheafRestrictScalarsUnitMap R S g))
      (leftDerivedTensorRightIso _) (leftDerivedTensorRightIso _) _
      (leftDerivedTensorRightUpperStarMap_app_comp g _) _
  exact isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isIso_mateEquiv
    R S g M

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **Derived extension of scalars along a dualizable algebra commutes with `Rf_*`**: for a ring
homomorphism `ρ : Λ →+* Λ'` such that the constant complex `Λ'_Y` of `Λ`-modules is dualizable,
the base change map `(Rf_* K) ⊗ᴸ_Λ Λ' ⟶ Rf_* (K ⊗ᴸ_Λ Λ')` is an isomorphism for every morphism
`f : X ⟶ Y` and every `K ∈ D(X_ét, Λ)`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y
      ((ModuleCat.restrictScalars.{u + 1} ρ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap ρ f).app K) := by
  let := ρ.toAlgebra
  exact isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isDualizable
    Λ Λ' f hΛ' K

/-- The `Λ`-module underlying the unit `Λ/J`-module is `Λ/J`. -/
noncomputable def restrictScalarsQuotientMkUnitIso (J : Ideal Λ) :
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J)).obj
        (𝟙_ (ModuleCat.{u + 1} (Λ ⧸ J))) ≅ ModuleCat.of Λ (Λ ⧸ J) :=
  LinearEquiv.toModuleIso (X₁ := (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J)).obj
      (𝟙_ (ModuleCat.{u + 1} (Λ ⧸ J)))) (X₂ := Λ ⧸ J)
    { toFun := id
      invFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }

/-- **Reduction modulo a power of a nonzerodivisor commutes with `Rf_*`**: for a nonzerodivisor
`ϖ` of `Λ` and `n : ℕ`, the base change map `(Rf_* K) ⊗ᴸ_Λ Λ/ϖⁿ ⟶ Rf_* (K ⊗ᴸ_Λ Λ/ϖⁿ)` is an
isomorphism for every morphism `f : X ⟶ Y` and every `K ∈ D(X_ét, Λ)`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) f).app
      K) :=
  isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable _ f
    ((isDualizable_constantSingle_quotient_span_pow hϖ n Y).of_iso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf _ _).mapIso
        (restrictScalarsQuotientMkUnitIso _).symm))) K

/-- For a `Λ`-algebra `Λ'`, the `Λ`-module underlying the unit `Λ'`-module is `Λ'`. -/
noncomputable def restrictScalarsAlgebraMapUnitLinearEquiv [Algebra Λ Λ'] :
    Λ' ≃ₗ[Λ] (ModuleCat.restrictScalars.{u + 1} (algebraMap Λ Λ')).obj
      (𝟙_ (ModuleCat.{u + 1} Λ')) where
  toFun := id
  invFun := id
  map_add' _ _ := rfl
  map_smul' r x := Algebra.smul_def r x
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Finite free extension of scalars commutes with `Rf_*`**: for a `Λ`-algebra `Λ'` which is
finite free as a `Λ`-module, the base change map `(Rf_* K) ⊗ᴸ_Λ Λ' ⟶ Rf_* (K ⊗ᴸ_Λ Λ')` is an
isomorphism for every morphism `f : X ⟶ Y` and every `K ∈ D(X_ét, Λ)`: the constant complex
`Λ'_Y` is dualizable (`AlgebraicGeometry.Etale.isDualizable_constantSingle`). -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_free [Algebra Λ Λ']
    [Module.Free Λ Λ'] [Module.Finite Λ Λ'] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap (algebraMap Λ Λ') f).app K) :=
  have := Module.Finite.equiv (restrictScalarsAlgebraMapUnitLinearEquiv (Λ := Λ) (Λ' := Λ'))
  have := Module.Projective.of_equiv (restrictScalarsAlgebraMapUnitLinearEquiv (Λ := Λ) (Λ' := Λ'))
  isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable _ f
    (isDualizable_constantSingle Y _) K

end AlgebraicGeometry.Etale
