/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonTensor
public import Sheaf.Paper.RationalComparisonScalarSquare
public import Sheaf.Paper.RationalComparisonTransitionTensor

/-! # The concrete rational comparison datum

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-datum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures.TensorComparisonDescent
attribute [local semireducible] FieldOf integerRing
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]
variable {C} (A : IntegralData C) (hA : A.Valid)


attribute [local instance] rationalStructures

/-- Assemble the actual balanced functors and normalized scalar comparisons.
The objects and maps are all constructed explicitly in the preceding modules.
Source: blueprint order 1826, steps 1--5
(blueprint: lem-sf-rational-comparison-datum). -/
@[irreducible] def rationalDatum : RationalData C A where
  F := rationalFunctor A hA
  object _ _ := rfl
  perfect := rationalFunctor_perfect A hA
  finite := rationalFunctor_finite A hA
  tensor := rationalFunctorCore A hA
  S := rationalStageSystem A hA
  transitionObject _ _ := rfl
  transitionTensor := rationalTransitionCore A hA
  identity := rationalTransitionIdentity A hA
  extendedPerfect := rationalFunctor_extendedPerfect A hA
  kappa a := DerivedCategory.PerfectScalar.fieldScalarComparison (fieldMap l Ω a).hom
  phi a := rationalPhi A hA a

end WeilConjectures.TensorComparisonDescent
