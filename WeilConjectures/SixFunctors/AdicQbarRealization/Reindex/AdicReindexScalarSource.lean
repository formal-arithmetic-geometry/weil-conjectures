/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicRealizationIntegralReindex
public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceConstruction
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceSquare

/-! # The source half of the integral realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-source)
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
/-- Coefficient enlargement for the source half of the comparison.
Only R occurs: there is no target realization S, ring reindexing B, or IntegralReindex.
Source: BS Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindex-scalar-source).

Proof in words: expand the source comparison at E and L. The normalized common-stage
pullback sends the coefficient arrow to the rational pullback scalar comparison,
conjugated by its stage identifications. Its integral representative is the prescribed
integral pullback scalar comparison. The common_field equation of R identifies the
other transition with the canonical balanced scalar associator followed by the
finite-free completion map. Naturality of that associator moves the E completion
comparison across it. The scalar square of the actual completion-unit comparison
identifies the resulting two whole-cone maps: each quotient coaugmentation has zero
shifted coordinate, and exact inverse image preserves both coordinates. Equivalently,
apply isomorphismComparison_scalarExtension after identifying podCompletedToTower
with the comparison normalized by inverse image of the actual unit. On complete
constructible inputs its two components are invertible, so cancel these components.
More explicitly, write p_E and p_L for podCompletedToTower, T for ordinary
scalar extension, χ for its completion map, and α for completed pullback/scalar
base change. The preceding normalized comparison gives
T_X(p_E) followed by χ_X followed by α =
b followed by G_L(χ_Y) followed by p_L, where b is completedScalarReindex.
Here scalarExactModel changes the exact ordinary tensor to the universal derived
tensor, and completedReindexModel changes only the equal coefficient-map presentation.
Invert p_E and p_L on these constructible inputs. Naturality of the native scalar
associator then moves native extension of p_E inverse past that associator.
Functoriality of native scalar extension gives the displayed square. Canonical equality
transports at the rational-stage endpoints compose to realizationScalarArrow. No cancellation of an
incomplete completion unit occurs. Repeated fields and empty schemes use exactly
the same normalized tensor and completion maps. -/
theorem realizationReindexSource_scalar (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let i := coefficientInclusion l (PadicAlgCl l) E L h
    let C := Coefficient.{u} l (PadicAlgCl l)
    let aX := pbcReductionNormalization (completedCoefficientMap l (C E) (C L) i X)
      (coefficientMap l X R L) (coefficientMap l X R E) (R.coefficient_scalar E L h)
    (commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R).map
        (realizationScalarArrow l Y E L h K) ≫
      (realizationReindexSource l g R L).hom.app
        ((integralTransition l (PadicAlgCl l) Y E L h).obj K) =
    (realizationReindexSource l g R E).hom.app K ≫
      (aX ((podCompletedDerivedInverseImage l (C E) g).obj K.obj)).inv ≫
      (pbcDerivedExtend (coefficientMap l X R L)).map
        ((completedScalarReindex l (C E) (C L) i g).hom.app K.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R L)).map
        ((podCompletedDerivedInverseImage l (C L) g).map
          ((completedScalarComparison l (C E) (C L) i Y).app K.obj)) := by
  dsimp only
  exact sourceScalarDiagram_square l g R E L h K

end WeilConjectures.AdicQbarRealization
