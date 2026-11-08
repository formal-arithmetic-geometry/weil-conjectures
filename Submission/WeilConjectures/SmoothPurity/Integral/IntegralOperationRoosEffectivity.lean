/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import Submission.WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Submission.WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import Submission.WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
import Submission.WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import Submission.WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import Submission.WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all Submission.WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all Submission.WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
import Submission.WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosComparisonSupplement
import all Submission.WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all Submission.WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import Submission.WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import all Submission.WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Submission.WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import Submission.WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import Submission.WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import Submission.WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Effectivity of the strict finite-operation towers

Source: Stacks Tags 099M and 099N(5); Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-pur-integral-operation-roos-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical projection of the strict Roos complex to its nth tower term.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-preserve-constructible).
It is the first mapping-cocone projection followed by the nth product projection. -/
def integralOperationRoosProjection (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (integralOperationsRoos T) ⟶ DerivedCategory.Q.obj (T.obj (op n)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
        (integralOperationsTowerStep T)) ≫ Pi.π (fun m ↦ T.obj (op m)) n)

local instance (priority := 4000) operationSiteSmall (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
local instance (priority := 4000) operationSequenceSmall (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) := essentiallySmallSelf.{u} _
private def operationDerivedAdjunction (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    scalarReductionDerivedExtension.{u, u} l E W n ⊣
      scalarReductionDerivedRestriction.{u, u} l E W n :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E W n).choose

private def operationOrdinaryAdjunction (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    scalarReductionExtension.{u, u} l E W n ⊣ scalarReductionRestriction.{u, u} l E W n :=
  (scalarReductionExtension_adjunction.{u, u} l E W n).choose

attribute [local irreducible] operationDerivedAdjunction operationOrdinaryAdjunction

private def operationFiniteFactors (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    DerivedCategory.Q ⋙ scalarReductionDerivedRestriction.{u, u} l E W n ≅
      (scalarReductionRestriction.{u, u} l E W n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (scalarReductionRestriction.{u, u} l E W n).mapDerivedCategoryFactors

attribute [local irreducible] scalarReductionDerivedExtension
  coefficientSequenceProjection coefficientSequenceLimit
attribute [local semireducible] coefficientSequenceLimit
attribute [local implicit_reducible] coefficientSequenceLimit
  coefficientConstantTowerEvaluation coefficientFiniteDerivedRestriction
attribute [local irreducible] coefficientConstantTowerLimit coefficientSequenceRestriction
  coefficientRestrictedEvaluationIso coefficientConstantTowerProjection

private def operationEffective (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (F : ∀ n : ℕ, CochainComplex (scalarReductionTarget.{u, u} l E W n) ℤ)
    (j : ∀ n : ℕ, T.obj (op n) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj (F n))
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (e : K ≅ DerivedCategory.Q.obj (integralOperationsRoos T)) : Prop :=
    IsSfDerivedComplete l E W K ∧ ∀ n : ℕ,
      IsIso (((operationDerivedAdjunction l E W n).homEquiv K
        (DerivedCategory.Q.obj (F n))).symm
        (e.hom ≫ integralOperationRoosProjection l E W T n ≫ DerivedCategory.Q.map (j n).hom ≫
          (operationFiniteFactors l E W n).inv.app
            (F n)))

attribute [local irreducible] operationEffective

attribute [local irreducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
attribute [local irreducible] unrestrictedIntegralComplexFunctor
attribute [local irreducible] scalarReductionExtension coefficientQuotientNatTrans
  unrestrictedIntegralTransition coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
attribute [local irreducible] coefficientSequenceEvaluation coefficientSequenceTransition
  unrestrictedIntegralReductionExistence
local instance (priority := 4000) operationScalarAdditive
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (scalarReductionExtension l E W n).Additive := scalarReductionExtensionAdditive l E W n

-- Literal endpoints keep scalar restriction from expanding coefficient actions
-- while comparing evaluation of a composite with successive evaluation.
private noncomputable def operationEvaluationIso
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  eqToIso (coefficientSequenceRestriction_evaluation l E W n)

attribute [local irreducible] operationEvaluationIso

/-- Keep the composite-restriction comparison behind its literal functor endpoints. -/
private noncomputable def operationRestrictionIso
    (W : AlgebraicGeometry.Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ scalarReductionRestriction l E W m ≅
      scalarReductionRestriction l E W n :=
  eqToIso (coefficientRestrictionComp l E W h)

attribute [local irreducible] operationRestrictionIso

private def restrictionComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (G : B ⥤ A) (G' : C ⥤ A) (H : C ⥤ B) (c : H ⋙ G ≅ G') (N : C) :
    G.obj (H.obj N) ≅ G'.obj N where
  hom := c.hom.app N
  inv := c.inv.app N
  hom_inv_id := c.hom_inv_id_app N
  inv_hom_id := c.inv_hom_id_app N

attribute [local semireducible] coefficientSequenceRestriction

-- Compare underlying section maps directly; transporting the old functor-level
-- square through scalar restriction would repeatedly unfold completed actions.
attribute [local irreducible] coefficientSequenceRestriction

attribute [local semireducible] operationDerivedAdjunction operationEffective

end WeilConjectures
