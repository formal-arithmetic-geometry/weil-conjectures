/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import all WeilConjectures.AlgebraicGeometry.FiniteGeneralRingOrientationAssembly
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingScalarUnitFormula

/-! Compatibility of scalar extension with the site-adjunction unit.
(blueprint: lem-sp-general-ring-scalar-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Scalar comparison carries the site unit to the target site unit.
Source: counit-preserving site comparison
(blueprint: lem-sp-general-ring-scalar-unit). -/
theorem scalarUnit_origin
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (Etale.scalarExtension φ T).map
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          (Etale.ordinaryFiniteUnit A T)) ≫
      Etale.FiniteSmoothPurity.originReductionMap φ T (finiteGeneralRingUnit A T) ≫
      (Etale.FiniteSmoothPurity.origin B T).map (finiteGeneralRingScalarUnitIso φ T).hom =
    (Etale.ExceptionalCoefficients.unitIso φ T).hom ≫
      (derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app
        (Etale.ordinaryFiniteUnit B T) := by
  exact scalarOriginUnit_comp
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) T)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} B) T)
    (Etale.scalarExtension φ T) (Etale.FiniteSmoothPurity.proScalar φ T)
    (pbcComparisonReduction T φ) (Etale.ordinaryFiniteUnit A T)
    (Etale.ordinaryFiniteUnit B T) (Etale.ExceptionalCoefficients.unitIso φ T).hom
    (finiteGeneralRingScalarUnitIso φ T).hom (scalarUnit_formula φ T)

end AlgebraicGeometry.ProEtale
