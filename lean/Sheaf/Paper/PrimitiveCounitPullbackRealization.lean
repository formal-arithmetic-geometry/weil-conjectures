/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.PrimitiveCounitComparisonModels

/-! # Pullback realization on strict quotient models

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, together with
strict quotient-system models and normalized Roos descent.
(blueprint: lem-pur-primitive-counit-pullback-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Completed inverse image is the total limit of inverse image of coherent reduction,
with its prescribed comparison on every good representative.
Source: Stacks Tag 0941; steps 1--3 of the primitive comparison argument.
(blueprint: lem-pur-primitive-counit-pullback-realization).

Proof: represent the coherent reduction of a flat-term K-flat input by its actual
strict quotient system. Apply the exact sequence inverse image. Its unit-normalized
finite evaluation comparison identifies the resulting restricted tower with the
pullback tower of the integral operation, including every transition. Normalized
Roos descent and the integral operation's representative comparison give the
isomorphism on good representatives. The localization universal property descends
it to every derived input and gives the displayed model equation. The normalization
on K-injective resolutions makes the comparison agree with the prescribed Roos
realization. This includes identity maps, zero inputs and empty schemes. -/
theorem primitiveCounitPullbackRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (ρ : PrimitiveCounit.RoosRealization l E X) :
    ∃ r : integralDerivedPullback l E f ≅
      S.reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X,
      PrimitiveCounit.PullModel l E f S ρ r := by sorry

end WeilConjectures
