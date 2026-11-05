/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Associativity of the normalized sequence pullback on cochains

Source: Stacks 07A4 and the total tensor construction, Tag 06YN.
(blueprint: lem-pur-completed-pullback-tensor-cochain-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] pullbackTensorSequenceInverse pullbackTensorSequenceAdjunction
  pullbackTensorSequenceCochain pullbackTensorSequenceRing Functor.leftAdjoint
  SheafOfModules.monoidalCategory HasDerivedCategory.standard
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
attribute [local implicit_reducible] pullbackTensorSequenceDirect Functor.mapHomologicalComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Pasting the six pure-section equations requires only function congruence.
Source: the pure-tensor calculation of Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-cochain-associativity). -/
private theorem associativitySectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

end WeilConjectures
