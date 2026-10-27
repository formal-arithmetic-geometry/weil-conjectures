/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.PodCompletionTensorNormalization

/-! # Completed tensor extension of a normalized completion comparison

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-construction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard


universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Extend a fixed normalized completion comparison to completed tensor.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-tensor-construction).

Proof: on simultaneous flat-term K-flat P,Q, use the quotient maps in D and the
sectionwise balanced tensor comparison to relabel every (p,q) summand. The two
orders of applying a quotient transition agree on x tensor y, so these maps
assemble into an isomorphism of strict towers. The inverse relabels in reverse.
Both differentials send a generator to dx tensor y + (-1)^p x tensor dy, proving
that these are chain maps. Their naturality follows on the same generators.
Reindexing preserves the common cohomological interval and constructibility of
every finite reduction. The Roos comparison in D and its limit model transport
derived completeness, so it preserves the complete constructible domain.
Apply D.roos followed by the tower isomorphism, and descend along the two K-flat
localizations to define the tensor isomorphism. This gives Model and Naturality.
The finite generator formula is the canonical finite pullback/tensor map.
D.Unit and D.Counit compare its whole-system realization with the specified
completed pullback comparison, proving Canonical before finite evaluation.
These constructions also apply to zero complexes and empty schemes. -/
theorem podReindexingTensorConstruction
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D) :
    ∃ T : PodCompletedTensorReindex l E g D,
      PodCompletedTensorReindex.Laws l E g D T := by sorry

end WeilConjectures
