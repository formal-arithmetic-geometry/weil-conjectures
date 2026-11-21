/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import WeilConjectures.Algebra.Homology.System.SystemCoproducts
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedComposition
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionUnit
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedTransition
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedCompositionEvaluation

/-! # Derived left extensions of strict semilinear systems

## References

* Stacks Project, Tags 06XN, 0FND, 09T5
* Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

-- Unused-variable linting needlessly normalizes the entire extension schema here.
set_option linter.unusedVariables false in
/-- Derived left extensions of arbitrary strict semilinear ring-sheaf systems.
The nonnegative index n denotes the positive index n+1. All structure fields
are conclusions: no flatness of the coefficient maps, normalization, or boundedness
is an assumption. The ordinary and derived universal properties determine each left
extension, with its actual unit and counit; normalized Hom formulas specify all
coefficient comparisons and the selected transition, including repeated next indices. -/
theorem systemLevelLeftExtensionTheory : Nonempty (SystemLevelLeftExtensionTheory (J := J)) := by
  classical
  let S : SystemScalarAssignment (J := J) := fun φ ↦ Classical.choice (nonempty_systemScalarModel φ)
  let T := systemTensorCoherence S
  let Sn := fun B n ↦ systemSingleDerivedExtension B n S T
  let Sr := fun B r ↦ systemSelectedDerivedExtension B r S T
  refine ⟨{ scalar := S
            tensor := T
            grothendieck := strictRingSystem_isGrothendieckAbelian
            coproducts := fun B ↦ inferInstance
            derivedCoproducts := strictRingSystem_derivedCoproducts
            levelDerivedCoproducts := systemLevel_derivedCoproducts
            evaluationCoproducts := fun B n I ↦ by
              have (m : ℕ) : HasColimitsOfShape (Discrete I) (systemLevel B m) := by
                have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
                    (derivedChangeRingIndependentCoefficients J (B.obj (op m))).obj) :=
                  PresheafOfModules.hasColimitsOfShape _ _
                exact
                  instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
              exact systemEvaluation_colimitsOfShape B (Discrete I) n
            derivedEvaluationCoproducts := derivedSystemEvaluation_coproducts
            cohomology := systemDerivedCohomology
            detectsIso := systemDerivedEvaluation_isIso_iff
            detectsBounds := systemDerivedEvaluation_bounds_iff
            single := Sn
            singleBelow := fun B {m n} h ↦ systemSingleBelow S T B n h
            singleAbove := fun B m n h P ↦ systemSingleLevelAbove S B n P h
            singleTranspose := fun B {m n} h ↦ systemSingleTranspose S T B n h
            singleDerivedBelow := fun B {m n} h ↦ systemSingleDerivedBelow B h S T
            singleDerivedAbove := fun B m n ↦ systemSingleDerivedAbove S T B m n
            transition := fun B {m n} h ↦ systemDerivedTransition B h
            transition_rep := fun B {m n} h ↦ systemDerivedTransition_rep B h
            transition_identity := fun B n ↦ systemDerivedTransition_tensorUnit B S n
            singleDerivedTranspose := fun B {m n} h ↦ systemSingleDerivedTranspose S T B h
            selected := Sr
            selectedEvaluation := systemDerivedSubsequenceEvaluation
            selectedEvaluation_rep := systemDerivedSubsequenceEvaluation_rep
            selectedBelow := fun B r m ↦ systemSelectedBelow S T B r m
            selectedTranspose := fun B r m ↦ systemSelectedTranspose S T B r m
            selectedDerivedBelow := fun B r m ↦ systemSelectedDerivedBelow B r m S T
            selectedDerivedTranspose := fun B r m ↦ systemSelectedDerivedTranspose S T B r m
            selectedTransition := systemSelectedDerivedTransition S
            restrictionComposition := systemDerivedSubsequenceComposition
            restrictionComposition_rep := systemDerivedSubsequenceComposition_rep
            extensionComposition := systemSelectedDerivedComposition S T
            composition_mate := systemSelectedDerivedComposition_mate S T
            extensionComposition_eval := systemSelectedDerivedComposition_eval S }⟩

end SheafOfModules
