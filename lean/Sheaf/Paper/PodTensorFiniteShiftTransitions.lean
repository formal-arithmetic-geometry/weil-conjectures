/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.PodTensorFiniteSignedShifts

/-! # Quotient compatibility of the concrete finite tensor shift maps

Only the two adjacent quotient squares remain here. The finite comparison maps
are already explicit; their existence is not part of this statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

/-- The explicit first- and second-factor finite tensor shifts commute with each
adjacent quotient transition.

Source: Stacks 011G, 07A4; more-algebra.tex, item-shift-tensor; blueprint
prop-pod-dual-tate-data-compatibility, Steps 1 and 5
(blueprint: lem-pod-tensor-finite-shift-transitions).

Proof: in each total degree test both composites on a homogeneous pure tensor
in the (p,q)-summand at level n + 1. The defining tensor-transition formula applies
the two coefficient reductions to its factors. First identify the two shifted
coefficient-reduction transitions by their
scalar-extension generator formulas and the uniqueness of those transitions.
The first-factor shift relabels
(p,q) to (p + r,q) with coefficient one, so either order gives that same reduced
pure tensor. The second-factor shift relabels it to (p,q + r) with coefficient
(-1)^(p * r). Reduction is linear and p is unchanged by the second-factor shift,
so the same coefficient occurs on both paths. The ordinary reduction shift and
restriction shift comparisons have identity components. These observations
prove equality on presheaf pure tensors. Sheafification and the coproduct
inclusions extend the equality to every module term, and degreewise
extensionality gives equality of the cochain maps. The proof works for negative
shifts, zero complexes and unbounded complexes without any convergence argument. -/
theorem podTensorFiniteShiftTransitions (W : Scheme.{u}) :
    PodTensorFiniteShiftTransitions l E W := by
  sorry

end WeilConjectures
