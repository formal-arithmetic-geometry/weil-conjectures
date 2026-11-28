/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTransport
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.ProjectionPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionRestrictScalars

/-!
# Derived extension of scalars along a dualizable algebra commutes with `Rg_*`

Let `R` be a commutative ring and `S` an `R`-algebra. The base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension `Ψ = - ⊗ᴸ_R S` along the derived direct
image of pro-étale sheaves is the mate of the commutation of `Ψ` with `Lg^*`. Restricted back to
`R`, it is the projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ Lg^* S_Y)` for the constant sheaf
`S_Y`. The projection map is an isomorphism at every dualizable object, the derived pullback
being monoidal; hence the base change map is an isomorphism for every morphism `g` and every
`M` as soon as the constant complex `S_Y` is dualizable. This applies to the reduction
`Λ ⟶ Λ/ϖⁿ` modulo a power of a nonzerodivisor `ϖ` of an arbitrary commutative ring `Λ`.

## Main results

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarExtendScalarsMap`: the base change map
  `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable`:
  the projection map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` is an isomorphism for dualizable `L`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable`:
  the base change map is an isomorphism when the constant complex `S_Y` is dualizable.
- `AlgebraicGeometry.ProEtale.isDualizable_singleFunctor_constantSheaf_quotient_span_pow`: the
  constant complex `(R/ϖⁿ)_X` is dualizable for a nonzerodivisor `ϖ` of `R`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow`:
  the reduction `Λ ⟶ Λ/ϖⁿ` modulo a power of a nonzerodivisor commutes with `Rg_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section ProjectionFormula

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

/-- **The projection formula for `Rg_*` at a dualizable object.** For any morphism
`g : Z ⟶ Y`, the projection map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` of
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap` is an isomorphism when `L` is
dualizable: `Lg^*` is monoidal, with comonoidal structure the tensor comparison
(`CategoryTheory.Functor.leftDerivedFunctorMonoidal`). -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (M : DerivedCategory (Sheaf (ProEt.topology Z) A))
    {L : DerivedCategory (Sheaf (ProEt.topology Y) A)} (hL : IsDualizable L) :
    IsIso (((rightDerivedLowerStarProjectionMap A g).app M).app L) := by
  let := (ProEtale.upperStar A g).leftDerivedFunctorMonoidal
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf (ProEt.topology Y) A)
  exact (derivedUpperStarLowerStarAdjunction A g)
    |>.isIso_rightAdjointProjectionMap_app_app_of_isDualizable _ (fun _ _ ↦ rfl) M hL

end ProjectionFormula

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section LowerStar

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` of derived scalar extension along the derived
direct image: the mate of the commutation `Lg^* ∘ Ψ ≅ Ψ ∘ Lg^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`). -/
noncomputable def rightDerivedLowerStarExtendScalarsMap :
    R((g)_*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Y) ⟶
      L(sheafExtendScalars (algebraMap R S) Z) ⋙ R((g)_*[ModuleCat.{u + 1} S]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedUpperStarExtendScalarsIso R S g).hom

/-- The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` is an isomorphism at `M` as soon as the mate
`L(- ⊗ S_Y) (Rg_* M) ⟶ Rg_* (L(- ⊗ S_Z) M)` of the comparison
`Lg^* (K ⊗ᴸ S_Y) ⟶ Lg^* K ⊗ᴸ S_Z` is. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_mateEquiv
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))
    [IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app M)] :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app M) :=
  Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedSheafExtendScalarsAdjunction R S Y)
    (leftDerivedSheafExtendScalarsAdjunction R S Z) (leftDerivedUpperStarExtendScalarsIso R S g)
    (leftDerivedSheafExtendScalarsProjection R S Y) (leftDerivedSheafExtendScalarsProjection R S Z)
    (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)
    (fun X ↦ Adjunction.map_comp_mateEquiv_app_comp_map_of_transpose _ _ _ _ _ _ X
      (leftDerivedSheafExtendScalarsProjection_transpose_upperStar R S g X)) M

/-- The base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` is an isomorphism at `M` as soon as the
projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ Lg^* S_Y)` at the sheaf `S_Y` of `R`-modules
underlying the unit sheaf of `S`-modules is. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_projectionMap
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R)))
    (h : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app M).app
      (derivedSingle (sheafRestrictScalarsUnit R S Y)))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app M) := by
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)).app M).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) := h
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app M) :=
    Adjunction.isIso_mateEquiv_app_of_isIso_rightAdjointProjectionMap
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)
      (leftDerivedUpperStarDerivedSingleMap g (upperStarSheafRestrictScalarsUnitMap R S g))
      (leftDerivedTensorRightIso _) (leftDerivedTensorRightIso _) _
      (leftDerivedTensorRightUpperStarMap_app_comp g _) _
  exact isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_mateEquiv R S g M

/-- **Derived extension of scalars along a dualizable algebra commutes with `Rg_*`.** For an
`R`-algebra `S` such that the complex `S_Y` of `R`-modules underlying the unit sheaf of
`S`-modules is dualizable, and any morphism `g : Z ⟶ Y`, the base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` is an isomorphism for every `M`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable_derivedSingle
    (hS : IsDualizable (derivedSingle (sheafRestrictScalarsUnit R S Y)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app M) :=
  isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_projectionMap R S g M
    (isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable _ g M hS)

end LowerStar

section Unit

attribute [local instance] Sheaf.monoidalCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/-- The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_proét`
(`AlgebraicGeometry.ProEtale.sheafRestrictScalarsUnit`) is the constant sheaf with value `S`. -/
noncomputable def constantSheafIsoSheafRestrictScalarsUnit (X : Scheme.{u}) :
    (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S))) ≅
      sheafRestrictScalarsUnit R S X :=
  have : (ProEt.topology X).PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))
  ((constantCommuteCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).app _).symm ≪≫
    (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapIso
      (Functor.Monoidal.εIso (presheafToSheaf (ProEt.topology X) (ModuleCat.{u + 1} S))).symm

end Unit

/-- The complex `S_X[0]`, with `S_X` the sheaf of `R`-modules underlying the unit sheaf of
`S`-modules, is the constant complex with value `S` in degree `0`. -/
noncomputable def derivedSingleSheafRestrictScalarsUnitIso (X : Scheme.{u}) :
    derivedSingle (sheafRestrictScalarsUnit R S X) ≅
      (DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
          ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
            (𝟙_ (ModuleCat.{u + 1} S)))) :=
  (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))
      0).app (sheafRestrictScalarsUnit R S X)).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (constantSheafIsoSheafRestrictScalarsUnit R S X).symm

/-- **Derived extension of scalars along a dualizable algebra commutes with `Rg_*`.** For an
`R`-algebra `S` such that the constant complex `S_Y` of `R`-modules is dualizable in
`D(Y_proét, R)`, and any morphism `g : Z ⟶ Y`, the base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)`, the mate of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`, is an isomorphism for every
`M ∈ D(Z_proét, R)`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable {Y Z : Scheme.{u}}
    (g : Z ⟶ Y)
    (hS : IsDualizable
      ((DerivedCategory.singleFunctor (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)).obj
          ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
            (𝟙_ (ModuleCat.{u + 1} S))))))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app M) :=
  isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable_derivedSingle R S g
    (hS.of_iso (derivedSingleSheafRestrictScalarsUnitIso R S Y).symm) M

/-- For an `R`-algebra `S`, the `R`-module underlying the unit `S`-module is `S`. -/
noncomputable def restrictScalarsAlgebraMapUnitIso :
    (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S)) ≅
      ModuleCat.of R S :=
  (LinearEquiv.toModuleIso (X₁ := S) (X₂ := (ModuleCat.restrictScalars.{u + 1}
      (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S)))
    { toFun := id
      invFun := id
      map_add' _ _ := rfl
      map_smul' r x := Algebra.smul_def r x
      left_inv _ := rfl
      right_inv _ := rfl }).symm

variable {R} in
/-- For a nonzerodivisor `ϖ` of `R`, the constant complex `(R/ϖⁿ)_X` is dualizable in
`D(X_proét, R)`: the constant sheaf `(R/ϖⁿ)_X` is the cokernel of the multiplication
`ϖⁿ : R_X ⟶ R_X` (`DerivedCategory.sheafQuotPowShortComplex_shortExact`). -/
theorem isDualizable_singleFunctor_constantSheaf_quotient_span_pow {ϖ : R}
    (hϖ : ϖ ∈ nonZeroDivisors R) (n : ℕ) (X : Scheme.{u}) :
    IsDualizable
      ((DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
          (ModuleCat.of R (R ⧸ Ideal.span {ϖ} ^ n)))) :=
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact
    (DerivedCategory.sheafQuotPowShortComplex_shortExact (ProEt.topology X) hϖ rfl n)
    (isDualizable_unit.of_iso (Iso.refl _)) (isDualizable_unit.of_iso (Iso.refl _))

/-- **Reduction modulo a power of a nonzerodivisor commutes with `Rg_*`.** For a commutative
ring `Λ`, a nonzerodivisor `ϖ` of `Λ` and `n : ℕ`, the base change map
`(Rg_* M) ⊗ᴸ_Λ Λ/ϖⁿ ⟶ Rg_* (M ⊗ᴸ_Λ Λ/ϖⁿ)` is an isomorphism for every morphism `g : Z ⟶ Y` and
every `M ∈ D(Z_proét, Λ)`: the constant complex `(Λ/ϖⁿ)_Y` is dualizable
(`AlgebraicGeometry.ProEtale.isDualizable_singleFunctor_constantSheaf_quotient_span_pow`). -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_quotient_span_pow
    {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap Λ (Λ ⧸ Ideal.span {ϖ} ^ n) g).app M) :=
  isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isDualizable _ _ g
    ((isDualizable_singleFunctor_constantSheaf_quotient_span_pow hϖ n Y).of_iso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf _ _).mapIso
        (restrictScalarsAlgebraMapUnitIso _ _).symm))) M

end AlgebraicGeometry.ProEtale
