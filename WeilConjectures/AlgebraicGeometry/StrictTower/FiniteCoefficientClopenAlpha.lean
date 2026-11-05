/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenAlphaSiteTransport
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenTailSiteTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows

/-! # The coefficient comparison for the clopen alpha

Source: Stacks Project, Tags 03DA, 099R, 09AF and 07A7; the first two steps of
lem-cbc-single-level-finite-proper-open-transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B Λ : Type (u + 1)) [CommRing B] [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)

/-- The ordinary inverse pullback comparison, with its specified inverse.
Source: Stacks Tags 03DA and 099R
(blueprint: lem-cbc-finite-coefficient-clopen-alpha). -/
def hPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    H B Y Λ φ ⋙ modulePullback B f ≅
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ H B X Λ φ :=
  @asIso _ _ _ _ (hPullbackInv B f Λ φ) (hPullbackInv_isIso B f Λ φ)

section CoefficientAlphaProof

open CategoryTheory.Limits Opposite MateEvaluationScalars
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

private def fcPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    C B Y Λ φ ⋙ modulePullback B f ≅
      upperStar (ModuleCat.{u + 1} Λ) f ⋙ C B X Λ φ :=
  @asIso _ _ _ _
    ((mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (openBetaModuleAdj B f)).symm
        (TwoSquare.mk _ _ _ _ (cDirect B f Λ φ).hom)).natTrans
    (cPullback_isIso B f Λ φ)

private def fcOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    C B U Λ φ ⋙ moduleJ B j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙ C B X Λ φ :=
  @asIso _ _ _ _
    ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (moduleJAdj B j)).symm
        (TwoSquare.mk _ _ _ _ (fcPull B Λ φ j).inv)).natTrans
    (cOpen_isIso B j Λ φ)

attribute [local irreducible] C fcPull fcOpen modulePullback
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  upperStar upperStarLowerStarAdjunction upperStarComp upperStarCompIso upperStarCongr

attribute [local irreducible] scalarPaste scalarAlphaPaste ScalarCompatible
  Functor.leftAdjoint

attribute [local semireducible] upperStar upperStarLowerStarAdjunction modulePullback

attribute [local irreducible] modulePullback upperStar upperStarLowerStarAdjunction
  Etale.upperStar

private def fcHIso (X : Scheme.{u}) :
    H B X Λ φ ≅ comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙ C B X Λ φ :=
  Iso.refl _

attribute [local irreducible] H fcHIso

attribute [local semireducible] H

attribute [local irreducible] H

attribute [local irreducible] hOpen hPullbackIso singleAlpha

end CoefficientAlphaProof
end AlgebraicGeometry.ProEtale.StrictTower
