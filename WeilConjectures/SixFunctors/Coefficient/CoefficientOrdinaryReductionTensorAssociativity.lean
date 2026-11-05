/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorNormalization
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Associativity of the ordinary quotient-system tensor comparison

Source: Stacks 03EK, 07A4 and 0941.

The ordinary tensor comparison of the strict quotient system is compatible with the
native total associators before localization. Chain maps of strict systems are tested
on all finite evaluations; there the tensor comparison becomes the normalized scalar
tensor comparison, and both composites agree on unit insertions of triple generators.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  CategoryTheory.Functor.mapHomologicalComplex

section Formal

variable {A S L : Type*} [Category* A] [Category* S] [Category* L]
  (tA : A × A ⥤ A) (tS : S × S ⥤ S) (tL : L × L ⥤ L) (K : A ⥤ S) (Ev : S ⥤ L) (F : A ⥤ L)
  (θ : K ⋙ Ev ≅ F) (κ : tA ⋙ K ≅ K.prod K ⋙ tS)
  (e : ∀ X Y : S, Ev.obj (tS.obj (X, Y)) ≅ tL.obj (Ev.obj X, Ev.obj Y))
  (s : ∀ P Q : A, F.obj (tA.obj (P, Q)) ≅ tL.obj (F.obj P, F.obj Q))

end Formal

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

namespace OrdinaryQuotient

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso coefficientScalarTensorIso coefficientUniqueComparisonChoice
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology SheafOfModules.monoidalCategory

end OrdinaryQuotient

end WeilConjectures
