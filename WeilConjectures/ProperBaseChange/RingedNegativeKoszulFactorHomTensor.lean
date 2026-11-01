/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.ProperBaseChange.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Tensor-Hom comparison for one two-term Koszul factor

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free dual identification.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

section Generic

variable {E : Type*} [Category E] [MonoidalCategory E] [BraidedCategory E]
  [MonoidalClosed E]

omit [MonoidalClosed E] in
omit [BraidedCategory E] in
omit [BraidedCategory E] in
end Generic

section HomFunctor

variable {E : Type*} [Category E] [MonoidalCategory E] [BraidedCategory E]

end HomFunctor

section GenericComplex

variable {B : Type w} [Category.{v} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  [HasColimitsOfSize.{0, 0} B]

omit [MonoidalClosed B] [BraidedCategory B] in
attribute [local instance] genericComplexTensorExists

attribute [local instance] genericComplexMonoidal

attribute [local instance] genericComplexMonoidalStruct

end GenericComplex

attribute [local instance 20000] ringedCompletionHasSheafCompose

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

attribute [local irreducible] homComplexFunctor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance : MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

attribute [local instance] moduleMonoidal

attribute [local instance] moduleMonoidalStruct

attribute [local instance] complexTensorExists

attribute [local instance] complexMonoidal

attribute [local instance] complexMonoidalStruct ringedComplexClosed

private abbrev RHom (L M : ringedSiteComplex O) : ringedSiteComplex O :=
  ((homComplexFunctor (R := O)).obj (op L)).obj M

attribute [local irreducible] SheafOfModules.homObj SheafOfModules.homObjMap
  SheafOfModules.homObjUnitIso

attribute [local irreducible] ringedHomUnitEvaluationIso

attribute [local irreducible] ringedNegativeKoszulFactorTransition
  ringedNegativeKoszulFactorTransitionF ringedKoszulFactorStep ringedKoszulFactorStepF
  ringedKoszulFactorProjection ringedKoszulFactorProjectionF ringedNegativeKoszulFactorBasis

attribute [local irreducible] ringedKoszulFactor ringedNegativeKoszulFactor ringedKoszulScalar

attribute [local irreducible] MonoidalClosed.curry MonoidalClosed.curry'
  MonoidalClosed.pre

attribute [-instance] moduleMonoidalStruct moduleMonoidal complexTensorExists

end CategoryTheory
