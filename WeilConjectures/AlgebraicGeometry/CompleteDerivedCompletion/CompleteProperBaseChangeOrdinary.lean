/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteExchangeMap
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.Exact.ExactCondensedExchangeComparison
public import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ComapUpperStarIsoComposition
public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientExchangeEncoding
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedCounit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteExchangeOrdinaryCompatibility

/-!
# Ordinary proper base change from completed proper base change

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-proper-base-change/
sec-pbc-condensed/sk-rem-pbc-complete-ordinary.md and the final paragraph of
sk-prop-pbc-complete/sk-prop-pbc-complete.proof.md
(blueprint: sk-rem-pbc-complete-ordinary).

The comparison uses the canonical completion units of the two ordinary pullbacks.
The finite-reduction hypothesis is the one in completeProperBaseChange, including
an independently chosen lower bound at every positive level n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

/-- Under the hypotheses of completed proper base change, completeness of the two
ordinary pullbacks identifies the completed exchange with the ordinary exchange,
which is therefore invertible. The displayed square expresses this identification
using the specified completion maps, rather than arbitrary endpoint isomorphisms.

Source: sk-rem-pbc-complete-ordinary.md; final paragraph of
sk-prop-pbc-complete/sk-prop-pbc-complete.proof.md
(blueprint: sk-rem-pbc-complete-ordinary).

Proof:
1. Apply sk-prop-pbc-complete (completeProperBaseChange) to K. The derived limit of
   the finite-level exchange maps is invertible, and its identification with
   completedExchangeMap is the ordered composite of det-pbc-complete-exchange-map (2).
2. The completion units and the two exchange maps form the square asserted by
   lem-sfb-complete-exchange-ordinary-compatibility. Both exchanges are the same
   unit--pullback-comparison--counit mate, before and after reduction and derived limit;
   naturality with the quotient maps and the (π,1) transitions gives the square.
3. By det-pbc-complete-derived-completion, notation (4), and
   lemma-weil-pbc-completed-pullback-reduction (3), hsource and htarget make the two
   completedPullUnit components invertible. Applying Rp'_* to the latter preserves
   invertibility. Equivalently, prop-weil-pbc-direct-image-limits (3) identifies the
   target completion map with this image. Cancel the two vertical isomorphisms in
   step 2. Thus ordinary exchange is invertible and identifies with completed exchange.
-/
theorem completeProperBaseChange_ordinary
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hcomplete : IsDerivedComplete l E X K)
    (hclassical : ∀ n : ℕ,
      (∃ b : ℤ, ((AdicCompletion.derivedReduction l E X n).obj K).IsGE b) ∧
      ∀ q : ℤ, IsClassicalModuleSheaf
        ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
          (AdicCompletion.finiteRing l E X n)).functor.obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((AdicCompletion.derivedReduction l E X n).obj K))))
    (hsource : IsDerivedComplete l E Y'
      ((dpullModule l E g).obj ((rpushModule l E p).obj K)))
    (htarget : IsDerivedComplete l E X' ((dpullModule l E g').obj K)) :
    IsIso (completedExchangeMap l E sq.toCommSq K) ∧
      IsIso ((moduleExchange l E sq.toCommSq).app K) ∧
      (completedPullUnit l E g).app ((rpushModule l E p).obj K) ≫
          completedExchangeMap l E sq.toCommSq K =
        (moduleExchange l E sq.toCommSq).app K ≫
          (rpushModule l E p').map ((completedPullUnit l E g').app K) := by
  have hpb := completeProperBaseChange l E sq K hcomplete hclassical
  have hred_source := completedPull_reduction l E g
  have hred_target := completedPull_reduction l E g'
  have hunit_source :
      IsIso ((completedPullUnit l E g).app ((rpushModule l E p).obj K)) := by
    exact (hred_source.2.2.2 ((rpushModule l E p).obj K)).2.mpr hsource
  have hunit_target : IsIso ((completedPullUnit l E g').app K) := by
    exact (hred_target.2.2.2 K).2.mpr htarget
  have : IsIso ((completedPullUnit l E g).app ((rpushModule l E p).obj K)) := hunit_source
  have : IsIso ((completedPullUnit l E g').app K) := hunit_target
  have : IsIso ((rpushModule l E p').map ((completedPullUnit l E g').app K)) := inferInstance
  have hcompat := completeExchange_ordinary_compatibility l E sq K
  have : IsIso (completedExchangeMap l E sq.toCommSq K) := hpb.2.1
  have : IsIso ((moduleExchange l E sq.toCommSq).app K ≫
      (rpushModule l E p').map ((completedPullUnit l E g').app K)) := by
    rw [← hcompat]
    infer_instance
  have hmodule : IsIso ((moduleExchange l E sq.toCommSq).app K) :=
    IsIso.of_isIso_comp_right
      ((moduleExchange l E sq.toCommSq).app K)
      ((rpushModule l E p').map ((completedPullUnit l E g').app K))
  exact ⟨hpb.2.1, hmodule, hcompat⟩

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
