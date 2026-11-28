/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenScalarTransitionCompatibility
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearNaturalIsoAssembly

/-! # Natural strict-system assembly of the ordinary open tensor comparison

We assemble the normalized finite extension tensor comparisons into a natural isomorphism of
strict systems.

## References

* [Stacks, Tag 03DJ]
* [Stacks, Tag 0E8I]
* [Stacks, Tag 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.scalarReductionExtension
  WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  WeilConjectures.OpenSemilinearTensor.scalarLevelComparison
  WeilConjectures.IntegralOpenReduction.extensionEvaluation
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientSequenceTransition
  CategoryTheory.Functor.leftAdjoint CategoryTheory.constantSheaf
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.ofSequence
  CategoryTheory.Functor.ofOpSequence
attribute [local implicit_reducible] WeilConjectures.coefficientSequenceEvaluation
  WeilConjectures.SemilinearSections.evaluation
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf
  WeilConjectures.SemilinearSections.rings
  WeilConjectures.SemilinearSections.openTransitions
  CategoryTheory.Functor.sheafPushforwardContinuous
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.coefficientSequenceCommRingSystem
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.integralCoefficientSheaf
  CategoryTheory.sheafCompose
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)

private theorem extensionTransitions
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (tensor : TensorComparison l E j o)
    [EssentiallySmall.{max u (t + 1)} X.ProEt]
    (M : scalarReductionSource l E U) {m n : ℕ} (h : n ≤ m) :
    (SemilinearSections.transition (ProEt.topology X) (rings l E X)
      (transitions l E X) h).app ((extension l E j o ⋙ AX.functor).obj M) ≫
      (SemilinearSections.res (SemilinearSections.coefficientMap (ProEt.topology X)
        (rings l E X) (transitions l E X) h)).map
          ((OpenSemilinearTensor.scalarLevelComparison l E j o AX AU tensor n).hom.app M) =
      (OpenSemilinearTensor.scalarLevelComparison l E j o AX AU tensor m).hom.app M ≫
        (SemilinearSections.transition (ProEt.topology X) (rings l E X)
          (transitions l E X) h).app ((AU.functor ⋙ systemExtension l E j o).obj M) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  exact OpenSemilinearTensor.openScalarTransitionCompatibility
    l E j o AX AU o.openSystems.restrictionSections tensor M h

-- Reconcile the concrete coefficient categories without unfolding chosen scalar functors.
/-- Assemble the normalized finite extension tensor comparisons as a strict-system iso
whose evaluation at each level `n` is the finite comparison. -/
theorem ordinaryExtensionTensorAssembly
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (tensor : TensorComparison l E j o) :
    ∃ r : extension l E j o ⋙ AX.functor ≅ AU.functor ⋙ systemExtension l E j o,
      ∀ M n, (coefficientSequenceEvaluation l E X n).map (r.hom.app M) =
        (OpenSemilinearTensor.scalarLevelComparison l E j o AX AU tensor n).hom.app M := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  refine SemilinearSections.naturalIsoOfEvaluation_exists (ProEt.topology X)
    (rings l E X) (transitions l E X)
    (extension l E j o ⋙ AX.functor) (AU.functor ⋙ systemExtension l E j o)
    (OpenSemilinearTensor.scalarLevelComparison l E j o AX AU tensor) ?_
  intro M m n h
  exact extensionTransitions l E j o AX AU tensor M h

end WeilConjectures.CanonicalOpenRestriction
