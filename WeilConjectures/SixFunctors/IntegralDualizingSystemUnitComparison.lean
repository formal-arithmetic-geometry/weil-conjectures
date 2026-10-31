/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # The coefficient system unit and its finite evaluations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private def closedUnitIso {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S T : CoefficientClosedStructure H) :
    S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit :=
  (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    ((T.adjunction T.monoidal.tensorUnit).leftAdjointUniq
      (S.adjunction T.monoidal.tensorUnit)).app S.monoidal.tensorUnit ≪≫
    S.monoidal.leftUnitor T.monoidal.tensorUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})

/-- A closed system tensor has the actual coefficient ring complex as unit.
Source: Stacks 07A4, 08J9; finite counit compatibility, proof step 2.
(blueprint: lem-coef-system-unit-comparison).
Proof: choose the already constructed closed derived tensor model, whose unit is the
coefficient ring in degree zero. For a fixed tensor parameter, both closed tensor
structures are left adjoints to the same internal Hom. Their unique left-adjoint
comparison, evaluated on the first unit, identifies the two units using their unitors.
Compose with the canonical model's coefficient-unit identification. -/
theorem integralDualizingSystemUnit_iso
    (T : CoefficientDerivedSystemTensors l E W) :
    Nonempty (T.systemClosed.monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
        (SheafOfModules.unit
          ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (coefficientSequenceCommRingSheaf l E W)))) := by
  obtain ⟨S, M, β, ⟨h⟩⟩ := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u}
    (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
  exact ⟨closedUnitIso T.systemClosed S ≪≫ h.unitIso⟩

/-- Pushforward along an identified ring preserves its regular module.
Source: Stacks 07A4 (blueprint: lem-coef-system-unit-comparison). -/
def integralDualizingPushforwardUnitIso {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    {S : Sheaf J RingCat.{u + 1}}
    (h : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R = S) :
    (SheafOfModules.pushforward (F := F) (eqToHom h.symm)).obj
      (SheafOfModules.unit R) ≅ SheafOfModules.unit S := by
  subst S
  exact Iso.refl _

/-- Ordinary evaluation sends the coefficient system ring to its finite regular module.
Source: Stacks 0941 (blueprint: lem-coef-system-unit-comparison). -/
def integralDualizingOrdinaryUnitEvaluation (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).obj
      (SheafOfModules.unit
        ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W))) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) :=
  integralDualizingPushforwardUnitIso (Prod.sectR n W.ProEt) _
    (coefficientSequenceEvaluationRing_eq l E W n)

/-- Canonical evaluation coordinates for the regular coefficient system.
Source: Stacks 07A4; finite counit compatibility, proof step 2.
(blueprint: lem-coef-system-unit-comparison). -/
def integralDualizingRegularUnitEvaluation (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).obj
      ((DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
        (SheafOfModules.unit
          ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (coefficientSequenceCommRingSheaf l E W)))) ≅
    (finiteDualizingRealization l E W n).obj
      (Etale.constantComplex (finiteDualizingCoeff l E n) W) :=
  ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (integralDualizingOrdinaryUnitEvaluation l E W n) ≪≫
    (finiteDualizingIntrinsicUnit l E W n).symm ≪≫
    ((sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
          (finiteDualizingCoeff l E n) W)).symm

end WeilConjectures
