/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
public import WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenSquareEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenUnitEvaluation
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- Coefficientwise evaluated tower mate identity.
Source: blueprint operations proof (2), finite open comparison and unit evaluation.
(blueprint: lem-sp-tower-open-alpha-evaluation).
Proof: apply the inverse mate evaluation identity, using the evaluated unit and
square identities and the finite transported mate identity. -/
theorem towerOpenAlphaEvaluation (b : Base l E) (o : Operations l E b)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (n : ℕ) (C : D l E U) :
    (Ev l E T' n).map ((towerOpenAlpha l E b o h j' j g sq.w).app C) ≫
        (towerOpenTargetEvaluation l E b o j g n).hom.app C =
      (towerOpenSourceEvaluation l E b o h j' n).hom.app C ≫
        (towerOpenFiniteBeta l E b h j' j g sq n).inv.app ((Ev l E U n).obj C) := by
  sorry
end AlgebraicGeometry.ProEtale.SpTowerShriek
