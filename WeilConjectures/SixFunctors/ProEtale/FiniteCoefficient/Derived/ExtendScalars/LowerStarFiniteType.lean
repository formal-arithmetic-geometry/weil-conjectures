/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStar

/-!
# Derived scalar extension commutes with `Rg_*` for `g` of finite type

Let `R` be a finite commutative ring, `S` an `R`-algebra and `g : Z ⟶ Y` a quasi-compact
quasi-separated morphism of schemes whose étale higher direct images of sheaves of `R`-modules
vanish above some degree `d`. For `K ∈ Dᵇctf(Z_proét, R)` the base change map
`Ψ (Rg_* K) ⟶ Rg_* (Ψ K)` of derived scalar extension `Ψ = - ⊗ᴸ_R S`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarExtendScalarsMap`) is an isomorphism
(`isIso_rightDerivedLowerStarExtendScalarsMap_app_of_cohomologicalDimension`).
Restricted back to `R`, it is the projection map `Rg_* K ⊗ᴸ S_Y ⟶ Rg_* (K ⊗ᴸ Lg^* S_Y)` for
the constant sheaf `S_Y`. Writing `K = ν^* K₀`, this is the pro-étale realization of the étale
projection map at the constant complex `S_Y`, an isomorphism by the projection formula for
constant coefficients along morphisms of finite cohomological dimension (Stacks 0F12,
`Etale.isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension`).
This removes the properness assumption of
`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app`.

For a morphism of schemes of finite type over a field the vanishing bound holds (Stacks 0F10,
`AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism`), which gives blueprint
`lemma-change-coefficients-direct-image--1`
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarExtendScalarsMap_app_of_finiteType`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section Unit

attribute [local instance] Sheaf.monoidalCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/-- The pro-étale realization of the constant étale sheaf with value `S` is the sheaf `S_X` of
`R`-modules underlying the unit sheaf of `S`-modules on `X_proét`. -/
noncomputable def comparisonUpperStarConstantSheafIsoSheafRestrictScalarsUnit (X : Scheme.{u}) :
    (ν^*(X)[ModuleCat.{u + 1} R]).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S)))) ≅
      sheafRestrictScalarsUnit R S X :=
  have : (ProEt.topology X).PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap R S))
  (comparisonUpperStarConstantSheafIso R X).app _ ≪≫
    ((constantCommuteCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).app _).symm ≪≫
    (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapIso
      (Functor.Monoidal.εIso (presheafToSheaf (ProEt.topology X) (ModuleCat.{u + 1} S))).symm

end Unit

variable [Finite R] {Y Z : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (d : ℕ)
  (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ), d < q →
    IsZero (((Etale.lowerStar (ModuleCat.{u + 1} R) g).rightDerived q).obj F))

include hd in
/-- **The projection formula at `S_Y` along a morphism of finite cohomological dimension.**
For a finite ring `R`, a quasi-compact quasi-separated `g` whose étale higher direct images
vanish above `d` and `K ∈ Dᵇctf(Z_proét, R)`, the projection map
`Rg_* K ⊗ᴸ S_Y ⟶ Rg_*(K ⊗ᴸ Lg^* S_Y)` is an isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_derivedSingle_of_cohomologicalDimension
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) Z K) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) g).app K).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) := by
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK.1
  obtain ⟨a, b, hKt⟩ := hK.2
  let c₀ := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj (𝟙_ (ModuleCat.{u + 1} S)))
  let L₀ := (_root_.DerivedCategory.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj c₀
  have hL₀ : _root_.DerivedCategory.TStructure.t.bounded L₀ :=
    ⟨⟨0, inferInstanceAs (_root_.DerivedCategory.IsGE L₀ 0)⟩,
      ⟨0, inferInstanceAs (_root_.DerivedCategory.IsLE L₀ 0)⟩⟩
  have hM₀ : _root_.DerivedCategory.TStructure.t.plus K₀ := hK₀.1.1
  let eM : K ≅ L(ν^*(Z)[ModuleCat.{u + 1} R]).obj K₀ :=
    eK.symm ≪≫ ((ν^*(Z)[ModuleCat.{u + 1} R]).leftDerivedFunctorIsoMapDerivedCategory.app K₀).symm
  let eL := ((ν^*(Y)[ModuleCat.{u + 1} R]).leftDerivedFunctorIsoMapDerivedCategory.app L₀).symm
  have hML := plus_derivedTensor_leftDerivedUpperStar_of_comparison_of_torAmplitudeIn g eM eL
    hKt ((ν^*(Y)[ModuleCat.{u + 1} R]).bounded_mapDerivedCategory_obj hL₀)
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_constantSingle_of_cohomologicalDimension
    R g d hd K₀ ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
      (𝟙_ (ModuleCat.{u + 1} S)))
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived (ModuleCat.{u + 1} R) g
    K₀ L₀ hM₀ hML
  exact NatTrans.isIso_app_app_of_iso _ eM.symm
    (eL.symm ≪≫ ((ν^*(Y)[ModuleCat.{u + 1} R]).mapDerivedCategorySingleFunctor 0).app c₀ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (comparisonUpperStarConstantSheafIsoSheafRestrictScalarsUnit R S Y) ≪≫
      (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).symm.app
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (sheafRestrictScalarsUnit R S Y)))

include hd in
/-- **Derived scalar extension commutes with `Rg_*` for `g` of finite cohomological dimension.**
For a finite ring `R`, an `R`-algebra `S`, a quasi-compact quasi-separated `g : Z ⟶ Y` whose
étale higher direct images of sheaves of `R`-modules vanish above `d`, and
`K ∈ Dᵇctf(Z_proét, R)`, the base change map `Ψ (Rg_* K) ⟶ Rg_* (Ψ K)` is an isomorphism. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_cohomologicalDimension
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) Z K) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app K) := by
  have : IsIso ((((derivedUpperStarLowerStarAdjunction _ g).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)).app K).app
        (derivedSingle (sheafRestrictScalarsUnit R S Y))) :=
    isIso_rightDerivedLowerStarProjectionMap_app_app_derivedSingle_of_cohomologicalDimension
      R S g d hd hK
  have : IsIso ((mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)).app K) :=
    Adjunction.isIso_mateEquiv_app_of_isIso_rightAdjointProjectionMap
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) g)
      (leftDerivedUpperStarDerivedSingleMap g (upperStarSheafRestrictScalarsUnitMap R S g))
      (leftDerivedTensorRightIso _) (leftDerivedTensorRightIso _) _
      (leftDerivedTensorRightUpperStarMap_app_comp g _) _
  exact isIso_rightDerivedLowerStarExtendScalarsMap_app_of_isIso_mateEquiv R S g _

omit [QuasiCompact g] [QuasiSeparated g] in
/-- Blueprint `lemma-change-coefficients-direct-image--1` (**finite ring maps**): for a finite
ring `R`, an `R`-algebra `S` (i.e. a ring map `R →+* S`), a morphism `g : Z ⟶ Y` of schemes of
finite type over a field `k` (here: locally of finite type and quasi-compact over `k`) and
`K ∈ Dᵇctf(Z_proét, R)`, the comparison `(Rg_* K)_S ⟶ Rg_*(K_S)` is an isomorphism in
`D(Y_proét, S)`. -/
theorem isIso_rightDerivedLowerStarExtendScalarsMap_app_of_finiteType {k : Type u} [Field k]
    (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aZ)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) Z K) :
    IsIso ((rightDerivedLowerStarExtendScalarsMap R S g).app K) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian aZ
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  have : QuasiCompact g := quasiCompact_of_compactSpace g
  have : QuasiSeparated g := QuasiSeparated.of_quasiSeparatedSpace g
  obtain ⟨d, hd⟩ :=
    Etale.hasFiniteCohomologicalDimensionMorphism R isAddTorsion_of_finite aZ aY g hg
  refine isIso_rightDerivedLowerStarExtendScalarsMap_app_of_cohomologicalDimension R S g d.toNat
    (fun F q hq ↦ ?_) hK
  exact (hd F q (by omega)).of_iso
    ((Etale.lowerStar (ModuleCat.{u + 1} R) g).homologyRightDerivedFunctorObjSingleFunctorIso F
      q).symm

end AlgebraicGeometry.ProEtale
