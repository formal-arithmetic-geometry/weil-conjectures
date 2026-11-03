/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import all WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- Evaluated unit identity for the open tower mate.
Source: blueprint operations proof (2), unit evaluation.
(blueprint: lem-sp-tower-open-unit-evaluation).
Proof: Rewrite the evaluated open-unit theorem through exact localization and
normalize the pullback and open-extension functors. -/
theorem towerOpenUnitEvaluation (b : Base l E) (o : Operations l E b)
    (n : ℕ) {V W : Scheme.{u}} (i : V ⟶ W) [IsOpenImmersion i] (M : D l E V) :
      (Ev l E V n).map ((o.openOp i).derivedAdjunction.unit.app M) ≫
        ((o.geometry i).pullEvaluation n).hom.app ((openD l E b (o.openOp i)).obj M) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) i).map
          ((openEvaluation l E b (o.openOp i) n).hom.app M) =
        (exactLocalizationDerivedAdjunction (finiteOpenAdjunction l E b i n)).unit.app
          ((Ev l E V n).obj M) := by
  sorry
end AlgebraicGeometry.ProEtale.SpTowerShriek
