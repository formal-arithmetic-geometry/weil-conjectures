/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingOrdinaryScalarUnit

/-! Formula for scalar extension of the comparison-origin coefficient unit.
(blueprint: lem-sp-general-ring-scalar-unit-formula). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The fixed scalar-unit isomorphism is the site comparison followed by the
ordinary scalar-unit map.
Source: multiplication-normalized scalar unit, general-ring purity (1)
(blueprint: lem-sp-general-ring-scalar-unit-formula). -/
theorem scalarUnit_formula
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (finiteGeneralRingScalarUnitIso φ T).hom =
      (pbcComparisonReduction T φ).hom.app (Etale.ordinaryFiniteUnit A T) ≫
        (Etale.FiniteSmoothPurity.comparison B T).map
          (Etale.ExceptionalCoefficients.unitIso φ T).hom := by
  unfold finiteGeneralRingScalarUnitIso
  rw [Iso.trans_hom, Functor.mapIso_hom]
  exact congrArg (fun z ↦
    (pbcComparisonReduction T φ).hom.app (Etale.ordinaryFiniteUnit A T) ≫
      (Etale.FiniteSmoothPurity.comparison B T).map z) (ordinaryScalarUnitSandwich φ T)

end AlgebraicGeometry.ProEtale
