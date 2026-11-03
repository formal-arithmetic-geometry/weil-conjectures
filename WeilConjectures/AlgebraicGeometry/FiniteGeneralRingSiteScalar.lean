/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingScalarUnit
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothDiagonalScalar
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison

/-! Site/scalar compatibility at the ordinary coefficient unit.
(blueprint: lem-sp-general-ring-site-scalar). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The ordinary dualizing coefficient map and the site unit form a commuting square.
Source: general-ring purity, counit-preserving site comparison
(blueprint: lem-sp-general-ring-site-scalar). -/
theorem scalarDualizingUnit_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] :
    (Etale.FiniteSmoothPurity.proScalar φ X).map (finiteGeneralRingDualizingUnitMap A f) ≫
      Etale.FiniteSmoothPurity.proCoefficientMap φ f (finiteGeneralRingUnit A Y) ≫
      (Etale.FiniteSmoothPurity.exceptional B f).map
        (finiteGeneralRingScalarUnitIso φ Y).hom =
    (pbcComparisonReduction X φ).hom.app
        (Etale.dualizingComplex A f) ≫
      (Etale.FiniteSmoothPurity.comparison B X).map
        (Etale.ExceptionalCoefficients.dualizingScalarMap φ f) ≫
      finiteGeneralRingDualizingUnitMap B f := by
  let u := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app
    (Etale.ordinaryFiniteUnit A Y)
  have hs := (pbcComparisonReduction X φ).hom.naturality
    ((Etale.rightDerivedUpperShriek A f).map u)
  have hm := Etale.FiniteSmoothPurity.mate_naturality φ f u
  dsimp only [Etale.scalarExtension, Functor.comp_obj, Functor.id_obj] at hm
  have hu := scalarUnit_origin φ Y
  dsimp only [Etale.scalarExtension, Etale.FiniteSmoothPurity.origin,
    finiteGeneralRingUnit] at hu
  unfold finiteGeneralRingDualizingUnitMap Etale.FiniteSmoothPurity.proCoefficientMap
  simp only [Category.assoc]
  erw [reassoc_of% hs]
  dsimp only [Etale.FiniteSmoothPurity.comparison, Etale.FiniteSmoothPurity.exceptional,
    Etale.FiniteSmoothPurity.origin, Functor.comp_map, Functor.comp_obj,
    Etale.scalarExtension, finiteGeneralRingUnit]
  erw [← Functor.map_comp_assoc, reassoc_of% hm]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  erw [← (Etale.rightDerivedUpperShriek B f).map_comp, hu]
  simp only [Functor.map_comp, Category.assoc,
    Etale.ExceptionalCoefficients.dualizingScalarMap_eq]
  rfl


end AlgebraicGeometry.ProEtale
