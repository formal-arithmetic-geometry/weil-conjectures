/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClassCoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionTranspose
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# The reduction of the integral Tate twist in degree one: the constituents

This file collects the constituents of the computation of the transpose of the reduction
`β : Ψ(red_{n+1} 𝒪_{E,X}(1)) ≅ red_n 𝒪_{E,X}(1)` through the identifications
`red_m 𝒪_{E,X}(1) ≅ Λ_m(1)`:

* `Etale.tateSheafPowOneChangeMap`: the change of coefficients `Λ(1) ⟶ Res Λ'(1)` of the étale
  Tate sheaves (the `e`-th power map on the roots of unity), written on `tateSheafPow _ _ 1`, and
  its comparison with `Etale.tateTwistObjectOneChangeMap`
  (`Etale.tateObjectNatIsoSingleFunctor_hom_comp_tateSheafPowOneChangeMap`);
* the naturality of `Rν_* ν^* S[0] ≅ S[0]` in `S`
  (`ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso_hom_naturality`);
* `ProEtale.CondensedRing.integralTateTwistReadingIso`: the pro-étale part
  `Φ(red_m 𝒪_{E,X}(d)) ≅ ν^*(Λ_m(1)^{⊗ d})[0]` of `etaleReductionIntegralTateTwistIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] [NeZero (ringChar Λ)]
  [NeZero (ringChar Λ')] (e : ℕ) (he : ringChar Λ = ringChar Λ' * e)

/-- The change of coefficients `Λ_X(1) ⟶ Res Λ'_X(1)` of the Tate sheaves, written on the tensor
powers `tateSheafPow _ X 1`: through `tateSheafPow _ X 1 ≅ (μ_n ⊗ Λ)`, the `e`-th power map
`μ_n ⟶ μ_{n'}` (`n = n' e`) followed by the change of coefficients `μ_{n'} ⊗ Λ ⟶ μ_{n'} ⊗ Λ'`
(see `tateTwistObjectOneChangeMap`). -/
noncomputable def tateSheafPowOneChangeMap :
    tateSheafPow Λ X 1 ⟶ (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj (tateSheafPow Λ' X 1) :=
  (tateTwistSheafNatIso Λ X 1).inv ≫ (tateTwistSheafOneIso X Λ).hom ≫
    (extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫ (extendScalarsChangeMap ρ X).app _ ≫
    (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
      ((tateTwistSheafOneIso X Λ').inv ≫ (tateTwistSheafNatIso Λ' X 1).hom)

/-- `tateTwistObjectOneChangeMap` through the identifications `Λ_X(1) ≅ (tateSheafPow _ X 1)[0]`
(`tateObjectNatIsoSingleFunctor`). -/
lemma tateObjectNatIsoSingleFunctor_hom_comp_tateSheafPowOneChangeMap :
    (tateObjectNatIsoSingleFunctor Λ X 1).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (tateSheafPowOneChangeMap ρ X e he) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (tateObjectNatIsoSingleFunctor Λ' X 1).inv =
      tateTwistObjectOneChangeMap ρ X e he := by
  have h := ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor
    0).inv.naturality ((tateTwistSheafOneIso X Λ').inv ≫ (tateTwistSheafNatIso Λ' X 1).hom)
  dsimp only [Functor.comp_map] at h
  simp only [tateObjectNatIsoSingleFunctor, tateSheafPowOneChangeMap,
    tateTwistObjectOneChangeMap, tateTwistObjectOneIso, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (DerivedCategory.singleFunctor _ 0) (tateTwistSheafNatIso Λ X 1).hom,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp_assoc (DerivedCategory.singleFunctor _ 0)
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).map (tateTwistSheafOneIso X Λ').inv),
    ← Functor.map_comp (Sheaf.restrictScalars X.smallEtaleTopology ρ), reassoc_of% h,
    ← Functor.map_comp_assoc (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ),
    ← Functor.map_comp (DerivedCategory.singleFunctor _ 0), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  rfl

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The identification `Rν_* ν^* S[0] ≅ S[0]` (`rightDerivedComparisonLowerStarSingleFunctorIso`)
is natural in the étale sheaf `S`. -/
lemma rightDerivedComparisonLowerStarSingleFunctorIso_hom_naturality (Λ : Type (u + 1))
    [CommRing Λ] (X : Scheme.{u}) {S S' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : S ⟶ S') :
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
        ((DerivedCategory.singleFunctor _ 0).map (ν^*(X)[ModuleCat.{u + 1} Λ].map g)) ≫
      (rightDerivedComparisonLowerStarSingleFunctorIso Λ X S').hom =
    (rightDerivedComparisonLowerStarSingleFunctorIso Λ X S).hom ≫
      (DerivedCategory.singleFunctor _ 0).map g := by
  have hn := ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  simp only [rightDerivedComparisonLowerStarSingleFunctorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, asIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp_assoc]
  refine congrArg (_ ≫ ·) ?_
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.naturality _).symm

/-- **`Rν_* ν^* S[0] ≅ S[0]` commutes with the restriction of scalars**: through the base change
map `Res Rν_* ⟶ Rν_* Res` (`derivedRestrictScalarsCompComparisonLowerStarMap`), the commutations
of `Res` with `singleFunctor` and with `ν^*` (`restrictScalarsCompComparisonUpperStar`), the
restriction of scalars of the identification for `S` is the identification for `Res S`. -/
lemma map_rightDerivedComparisonLowerStarSingleFunctorIso_hom {Λ Λ' : Type (u + 1)} [CommRing Λ]
    [CommRing Λ'] [IsNoetherianRing Λ] (φ : Λ →+* Λ') (X : Scheme.{u})
    (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ' X S).hom =
      (derivedRestrictScalarsCompComparisonLowerStarMap φ X).app
          ((DerivedCategory.singleFunctor _ 0).obj (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S)) ≫
        (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          (((Sheaf.restrictScalars (ProEt.topology X) φ).mapDerivedCategorySingleFunctor 0).hom.app
              (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S) ≫
            (DerivedCategory.singleFunctor _ 0).map
              (inv ((restrictScalarsCompComparisonUpperStar φ X).app S))) ≫
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ X
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj S)).hom ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
          S := by
  sorry

end AlgebraicGeometry.ProEtale

