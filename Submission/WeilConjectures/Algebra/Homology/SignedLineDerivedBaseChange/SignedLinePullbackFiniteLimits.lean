/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
public import Submission.WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.SignedLineModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SignedLineSheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Exactness of coefficient-identified pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange

universe r
private theorem ringSheafification {E : Type u} [Category.{v} E]
    [EssentiallySmall.{r} E] (H : GrothendieckTopology E) :
    HasSheafify H RingCat.{r} ∧
      H.PreservesSheafification (CategoryTheory.forget RingCat.{r}) ∧
      H.PreservesSheafification (CategoryTheory.forget AddCommGrpCat.{r}) := by
  have : HasSheafify ((equivSmallModel.{r} E).inverse.inducedTopology H)
      RingCat.{r} := inferInstance
  have : ∀ X : Eᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{r} E).inverse.op) RingCat.{r} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : ∀ X : Eᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{r} E).inverse.op) (Type r) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : ((equivSmallModel.{r} E).inverse.inducedTopology H).PreservesSheafification
      (CategoryTheory.forget RingCat.{r}) := inferInstance
  have : ((equivSmallModel.{r} E).inverse.inducedTopology H).PreservesSheafification
      (CategoryTheory.forget AddCommGrpCat.{r}) := inferInstance
  exact ⟨hasSheafifyEssentiallySmallSite H RingCat.{r}, inferInstance, inferInstance⟩

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

end SheafOfModules.SignedLineDerivedBaseChange
