/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Derived extension of finite coefficients commutes with `Rf_*` for `f` of finite type

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings with `Λ` finite, and `f : X ⟶ Y` a
quasi-compact quasi-separated morphism of schemes whose higher direct images of étale sheaves of
`Λ`-modules vanish above some degree `d`. Then the base change map
`(Rf_* K) ⊗ᴸ_Λ Λ' ⟶ Rf_* (K ⊗ᴸ_Λ Λ')` on the étale site
(`AlgebraicGeometry.Etale.rightDerivedLowerStarExtendScalarsMap`) is an isomorphism for every
`K ∈ D(X_ét, Λ)`
(`isIso_rightDerivedLowerStarExtendScalarsMap_app_of_cohomologicalDimension`).
Restricted back to `Λ`, it is the projection map `Rf_* K ⊗ᴸ Λ'_Y ⟶ Rf_* (K ⊗ᴸ Λ'_X)` for the
constant sheaf `Λ'_Y`, an isomorphism by the projection formula for constant coefficients along
morphisms of finite cohomological dimension
(`isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension`,
Stacks 0F12). This removes the properness assumption of
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarExtendScalarsMap_app`.

For a morphism `f` of schemes of finite type over a field `k`, the vanishing bound holds since
`f` has finite cohomological dimension for torsion coefficients
(`AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism`, Stacks 0F10), which gives
blueprint `lemma-change-coefficients-direct-image--1` on the étale site
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_finiteType`).
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

section Unit

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_ét`
(`AlgebraicGeometry.Etale.sheafRestrictScalarsUnit`) is the constant sheaf with value `S`:
the unit sheaf is the sheafification of the constant presheaf, and restriction of scalars
commutes with sheafification. -/
noncomputable def constantSheafIsoSheafRestrictScalarsUnit :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S))) ≅
      sheafRestrictScalarsUnit R S X :=
  have : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))
  ((constantCommuteCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).app _).symm ≪≫
    (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapIso
      (Functor.Monoidal.εIso
        (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))).symm

/-- The complex `S_X[0]`, with `S_X` the sheaf of `R`-modules underlying the unit sheaf of
`S`-modules, is the constant complex with value `S` in degree `0`. -/
noncomputable def derivedSingleSheafRestrictScalarsUnitIso :
    derivedSingle (sheafRestrictScalarsUnit R S X) ≅
      constantSingle (ModuleCat.{u + 1} R) X
        ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S))) :=
  (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      0).app (sheafRestrictScalarsUnit R S X)).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (constantSheafIsoSheafRestrictScalarsUnit R S X).symm

end Unit

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (d : ℕ)
  (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ), d < q →
    IsZero ((((g)_*[ModuleCat.{u + 1} R]).rightDerived q).obj F))

include hd in
/-- **Derived extension of scalars commutes with `Rg_*` for `g` of finite cohomological
dimension.** For a finite ring `R`, an `R`-algebra `S` and a quasi-compact quasi-separated
`g : Z ⟶ Y` whose higher direct images vanish above `d`, the base change map
`Ψ (Rg_* M) ⟶ Rg_* (Ψ M)`, the mate of
`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`, is an isomorphism.
Restricted to `R`, it is the projection map `Rg_* M ⊗ᴸ S_Y ⟶ Rg_* (M ⊗ᴸ S_Z)` for the constant
sheaf `S_Y`. -/
theorem
    isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_cohomologicalDimension
    [Finite R] (M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom).app M) := by
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)).app M).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) :=
    (NatTrans.isIso_app_iff_of_iso
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app M)
      (derivedSingleSheafRestrictScalarsUnitIso R S Y)).2
      (isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension
        R g d hd M _)
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

/-- **Derived extension of finite coefficients commutes with `Rf_*`** along a quasi-compact
quasi-separated morphism `f` whose higher direct images of sheaves of `Λ`-modules vanish above
`d`: for a finite ring `Λ` and any `ρ : Λ →+* Λ'`, the base change map
`(Rf_* K) ⊗ᴸ_Λ Λ' ⟶ Rf_* (K ⊗ᴸ_Λ Λ')` is an isomorphism for every `K ∈ D(X_ét, Λ)`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_cohomologicalDimension [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap ρ f).app K) := by
  let := ρ.toAlgebra
  exact
    isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_cohomologicalDimension
    Λ Λ' f d hd K

/-- Blueprint `lemma-change-coefficients-direct-image--1` (**finite ring maps**), on the étale
site: for a homomorphism `ρ : Λ →+* Λ'` with `Λ` finite and a morphism `f : X ⟶ Y` of schemes of
finite type over a field `k` (here: locally of finite type and quasi-compact over `k`), the
comparison `(Rf_* K)_{Λ'} ⟶ Rf_*(K_{Λ'})` is an isomorphism for every `K ∈ D(X_ét, Λ)`. The
higher direct images of `f` vanish in large degrees (Stacks 0F10), so this is the projection
formula for constant coefficients (Stacks 0F12). -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_finiteType [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap ρ f).app K) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiSeparated f := QuasiSeparated.of_quasiSeparatedSpace f
  obtain ⟨d, hd⟩ := hasFiniteCohomologicalDimensionMorphism Λ isAddTorsion_of_finite aX aY f hf
  refine isIso_rightDerivedLowerStarExtendScalarsMap_app_of_cohomologicalDimension ρ f d.toNat
    (fun F q hq ↦ ?_) K
  exact (hd F q (by omega)).of_iso
    (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F q).symm

end AlgebraicGeometry.Etale
