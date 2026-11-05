/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCochainAssociativity

/-! # Associativity for coherent pullback tensor representatives

Source: Stacks 07A4, `lemma-pullback-tensor-product`, and 07A2,
`lemma-tensor-product-K-flat`.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] pullbackTensorCalculus
attribute [local implicit_reducible] pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorSystemModel
  coefficientSequenceInternalHom coefficientSequenceHasDerived CoefficientClosedStructure.tensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CochainComplex.IsKFlatIndependentCoefficients
  pullbackTensorSequenceInverse derivedInternalHomOfUniverses coefficientTotalTensor
  Functor.mapHomologicalComplex pullbackTensorSequenceCochain
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
