/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PointTransportConeComparisonDescent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Strict tower data for the integral point transport realization
Source: blueprint rational Frobenius integral model, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).
The original public names use the existing canonical tower presentations. Explicit
endomorphism types keep their exported types small; the underlying towers, transition
maps and product endomorphisms are unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 5000] integralTowerHasDerivedCategory

/-- The recorded small-Hom localization of the ordinary integral module category.
This named construction keeps instance arguments in exported statements short.
Source: Stacks 05RU, as in `CompletedStalk.moduleQ`
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
@[instance_reducible] def trfPointModuleHasDerivedCategory : HasDerivedCategory.{u + 1}
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- Termwise integral sections, with the recorded O_E action.
Source: blueprint clause (3) (blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSectionsComplex :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  PointTransportCone.sections D l E

/-- The evaluated quotient-induced tower, before any localization.
Source: blueprint clause (3), common K-flat model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceTower := PointTransportCone.reductionTowers D l E

/-- The evaluated strict tower Res_n g_n^*(P_n), with its coefficient-induced transitions.
Source: blueprint clause (3), completed pullback model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetTower := PointTransportCone.pullbackTowers D l E

/-- The specified 1-s on the evaluated source tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  PointTransportCone.reductionEnd D l E P

/-- The specified 1-s on the evaluated pullback tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    End (∏ᶜ fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((trfPointTargetTower D l E).obj P))

/-- The same 1-s before applying sections.
Source: blueprint clause (3), sectionwise product computation
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSheafTargetEnd
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    End (∏ᶜ fun n ↦
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj (op n)) :=
  towerTransitionEndomorphism
    (K := fun n ↦
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P))

end WeilConjectures
