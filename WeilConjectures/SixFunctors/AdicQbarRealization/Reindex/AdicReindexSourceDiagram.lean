/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceAssembly

/-! # Source-component equations for the concrete diagram

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-diagram)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  commonStageDerivedPullback rationalDerivedPullback

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

open ScalarSourceCalculus

attribute [local implicit_reducible] StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  integralScalarExtensionOfUniverses

-- Keep the selected comparison maps abstract while checking the final square.
attribute [local irreducible] completedScalarReindex completedReindexModel scalarExactModel
  integralPullbackScalarComparison podCompletedToTowerIso pbcReductionNormalization
  pbcReductionNormalizationHom pbcReductionTransition
  podCompletedToTower pbcDerivedScalarAdjunction
attribute [local implicit_reducible] ordinary coefficientMap
  LocallyFiniteAdicRealization.ringSheaf AlgebraicGeometry.Scheme.residueField

/-- Add the already proved source-component equations to the explicit diagram maps.
Source: BS Remark 6.8.15 and Proposition 6.8.14.
(blueprint: lem-sf-adic-reindex-source-diagram).
Proof: the parent record is sourceScalarMaps, and source_hom gives both proof fields. -/
def sourceScalarDiagram (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    ScalarSourceDiagram
      (DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) X))
      (DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) L) X))
      (DerivedCategory (modules l X R)) := by
  let KL := (integralTransition l (PadicAlgCl l) Y E L h).obj K
  exact {
    toScalarSourceMaps := sourceScalarMaps l g R E L h K
    sourceE := source_hom l g R E K
    sourceL := source_hom l g R L KL }

end WeilConjectures.AdicQbarRealization
