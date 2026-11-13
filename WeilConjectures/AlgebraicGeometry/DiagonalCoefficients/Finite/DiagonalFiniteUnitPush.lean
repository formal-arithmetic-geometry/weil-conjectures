/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteUnitPushCore

import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp

/-! # Finite realization of the coefficient-unit arrow
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint FiniteRealization.derivedUnit
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

/-- Finite realization preserves the canonical coefficient-unit adjunct. -/
theorem finite_unit_push
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] (Y : Scheme.{u})
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (D : DiagonalRightDerived (CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (hc : D'.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y))
    (hcanonical : IsCanonicalRightDerived
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) D' hc)
    (s : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY D D') :
    let t := s.derived.iso.hom ≫
      Functor.whiskerLeft eP.F.mapDerivedCategory (eqToIso hc).hom
    eY.F.mapDerivedCategory.map (coefficientUnitPush R Y D) ≫
        t.app (unit R (ProjectiveLine Y)) ≫
        (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map eP.derivedUnit =
    eY.derivedUnit ≫
        finiteUnitAdjunct A Y := by
  let t := s.derived.iso.hom ≫
    Functor.whiskerLeft eP.F.mapDerivedCategory (eqToIso hc).hom
  let i : eP.F.mapDerivedCategory.obj (unit R (ProjectiveLine Y)) ≅
      geoP1Unit A (ProjectiveLine Y) :=
    (eP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eP.unitIso ≪≫
        (finiteUnitComparison A (ProjectiveLine Y)).symm
  have hi : i.hom = eP.derivedUnit := by
    unfold i FiniteRealization.derivedUnit
    try unfold Functor.compIsoApp
    rfl
  have hicomp : i.inv ≫
      eP.F.mapDerivedCategory.map (𝟙 (unit R (ProjectiveLine Y))) ≫
        eP.derivedUnit = 𝟙 _ := by
    rw [eP.F.mapDerivedCategory.map_id]
    simp only [Category.id_comp]
    rw [← hi]
    exact i.inv_hom_id
  have h := finite_unit_push_square Y eY eP D D' hc hcanonical s
  dsimp [t] at h ⊢
  rw [eP.F.mapDerivedCategory.map_id] at h
  simp only [Category.id_comp] at h
  have hj :
      (((finiteUnitComparison A (ProjectiveLine Y)).hom ≫
          (DerivedCategory.singleFunctor _ 0).map eP.unitIso.inv) ≫
        (eP.F.mapDerivedCategorySingleFunctor 0).inv.app
          (Mod.regular (condensedRingObj R (ProjectiveLine Y)))) ≫
        eP.derivedUnit = 𝟙 _ := by
    simpa [i] using hicomp
  rw [hj, (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map_id] at h
  simpa only [Category.comp_id, Category.id_comp] using h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

end
