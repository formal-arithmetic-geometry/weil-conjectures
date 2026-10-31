/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingRoosModel
public import WeilConjectures.SixFunctors.CoefHomTowerScalarModel
public import WeilConjectures.SixFunctors.CoefTowerNaturalCurrying

/-! # The two strict mapping towers in integral duality

These are constructions in the derived category of strict module towers, before
taking inverse limits. No finite-level isomorphisms are lifted merely from their
evaluations, and no unspecified trace is chosen.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph.
(blueprint: def-coef-integral-dualizing-mapping-towers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped MonoidalClosed.FunctorCategory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Small-Hom localization of the same strict coefficient towers.
Source: Stacks 079P (blueprint: def-coef-integral-dualizing-mapping-towers). -/
abbrev integralDualizingSmallTower :=
  @DerivedCategory (coefPairingModules l E) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- Localization of strict tower complexes into the small-Hom model.
Source: Stacks 079P (blueprint: def-coef-integral-dualizing-mapping-towers). -/
abbrev integralDualizingSmallTowerQ :
    CochainComplex (coefPairingModules l E) ℤ ⥤ integralDualizingSmallTower l E :=
  @DerivedCategory.Q (coefPairingModules l E) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The unique comparison of localization models, on the same complexes and maps.
Source: Stacks 079P (blueprint: def-coef-integral-dualizing-mapping-towers). -/
def integralDualizingTowerEquivalence :
    integralDualizingSmallTower l E ≌ coefPairingDerived l E :=
  Localization.uniq (integralDualizingSmallTowerQ l E) DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefPairingModules l E) (.up ℤ))

/-- Global Hom into a strict completed-coefficient tower. Constant-ring sequence
modules realize the tower; their internal Hom and derived sections retain its index.
Source: blueprint prop-coef-integral-dualizing, first mapping-limit comparison;
Stacks 0B6E and 0941 (blueprint: def-coef-integral-dualizing-mapping-towers). -/
def integralDualizingMappingTower (X : Scheme.{u})
    (Z : DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E X)) :
    (sfIntegralConstructibleCategory l E X)ᵒᵖ ⥤ coefPairingDerived l E :=
  (sfIntegralConstructible l E X).ι.op ⋙
    (coefHomDerivedConstant l E X).op ⋙
      (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
        ((coefHomEquivalence l E X).inverse.mapDerivedCategory.obj Z) ⋙
          coefHomConstantDerivedSections l E X

/-- Hom from a constant coefficient complex into the actual quotient tower.
This uses the closed structure on strict derived towers, not a choice of a functor
having the desired finite evaluations.
Source: blueprint prop-coef-integral-dualizing, last mapping-limit comparison;
Stacks 08J9 and 0941 (blueprint: def-coef-integral-dualizing-mapping-towers). -/
def integralDualizingCoefficientHomTower :
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (integralDualizingCoefficients l E)))ᵒᵖ ⥤ coefPairingDerived l E :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
  ((Functor.const ℕᵒᵖ : ModuleCat.{u + 1} (integralDualizingCoefficients l E) ⥤
    coefPairingModules l E).mapDerivedCategory).op ⋙
      MonoidalClosed.internalHom.flip.obj
        ((DerivedCategory.singleFunctor (coefPairingModules l E) 0).obj
          (coefCurryingQuotients l E)) ⋙ (integralDualizingTowerEquivalence l E).functor

end WeilConjectures
