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
/-- Evaluated inverse square identity for the open tower mate.
Source: blueprint operations proof (2), finite open comparison.
(blueprint: lem-sp-tower-open-square-evaluation).
Proof: Apply inverse path evaluation to h ≫ j = j' ≫ g and simplify the
operation composition evaluations and the square definition. -/
def towerOpenFiniteSquare (_b : Base l E)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) (w : h ≫ j = j' ≫ g) (n : ℕ) :=
  proEtaleConstantRingPullbackComposition j' g (R l E n) ≪≫
    eqToIso (congrArg (fun f ↦ proEtaleConstantRingDerivedPullback (R l E n) f) w.symm) ≪≫
    (proEtaleConstantRingPullbackComposition h j (R l E n)).symm

theorem towerOpenSquareEvaluation (b : Base l E) (o : Operations l E b)
    {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) (w : h ≫ j = j' ≫ g) (n : ℕ) (N : D l E T) :
    (Ev l E U' n).map ((square l E b o h j' j g w).inv.app N) ≫
        ((o.geometry j').pullEvaluation n).hom.app ((pull l E b (o.geometry g)).obj N) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) j').map
          (((o.geometry g).pullEvaluation n).hom.app N) =
      ((o.geometry h).pullEvaluation n).hom.app ((pull l E b (o.geometry j)).obj N) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) h).map
          (((o.geometry j).pullEvaluation n).hom.app N) ≫
        (towerOpenFiniteSquare l E b h j' j g w n).inv.app ((Ev l E T n).obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
