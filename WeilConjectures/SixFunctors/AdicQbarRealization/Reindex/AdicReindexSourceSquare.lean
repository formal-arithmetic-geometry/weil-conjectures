/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceDiagram
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceHead
import WeilConjectures.SixFunctors.AdicQbarRealization.PodCompletedComparisonScalarSquare

/-! # The completed source scalar diagram square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-square)
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

set_option maxHeartbeats 1600000 in
-- The square compares several presentations of the derived scalar functors.
/-- Paste the head and completion squares in the concrete diagram.
Source: BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-square).
Proof: the head computation supplies the first diagram square. Invertibility of l
in residue fields makes it a unit in all stalks, so the completed comparison square
supplies the second. Apply the generic pasting theorem to these two proved equations. -/
theorem sourceScalarDiagram_square (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let d := sourceScalarDiagram l g R E L h K
    d.f ≫ d.srcL = d.srcE ≫ d.n d.E ≫ d.NL.map d.b ≫ d.NL.map d.c := by
  let C := Coefficient.{u} l (PadicAlgCl l)
  let i := coefficientInclusion l (PadicAlgCl l) E L h
  have hhead := source_scalar_head l g R E L h K
  dsimp only at hhead
  dsimp only [nativeScalarTransition] at hhead
  simp only [Category.assoc] at hhead
  have hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [Scheme.residueField, map_natCast] using
      (isUnit_of_invertible (l : X.residueField x)).ne_zero
  have hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := by
    intro y
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [Scheme.residueField, map_natCast] using
      (isUnit_of_invertible (l : Y.residueField y)).ne_zero
  have hsquare := completion_constructible_scalar_square l (C E) (C L) i g hX hY K
  exact (sourceScalarDiagram l g R E L h K).square
    hhead hsquare

end WeilConjectures.AdicQbarRealization
