/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefProjectionEvaluationData

/-! # Normalized coefficient point-sections comparisons

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6, 08J9, 0D6D and 0B56.
(blueprint: lem-sf-coef-projection-sections-models-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two normalized sections comparisons needed for projection-evaluation:
sections after native image, and the quotient/integral compact-support presentation.
No tensor structure, projection mate or internal-Hom comparison is asserted.

Source: Stacks 0D6D, 0D6E and 0941; projection-evaluation steps 2, 6 and 7.
(blueprint: lem-sf-coef-projection-sections-models-existence).

Proof: evaluate ordinary image followed by quotient sections at (n,Y). Pullback
of the terminal object is canonically terminal, so restriction along its inverse
identifies these sections with sections at (n,X). This is linear and natural in
both the module and n, hence defines SectionsComposition.ordinary with exactly
its section equation. The ringed-site derived direct-image composition theorem,
normalized by the universal right-derived units, gives its derived isomorphism
and DerivedCompositionNormalization. For the second comparison, the two ordinary
functors both evaluate the module at (n,Y). Their integral scalar actions agree
by the completion projection identity. The identity of underlying sections thus
gives SupportSections.ordinary and its HEq equation. Derive this ordinary square,
using exactness of point restriction to identify its derived functor with the
specified mapDerivedCategory. Derived composition gives precisely the displayed
unit equation. Finally retain the native SectionsModel from supportOpenTensorModel
(or sectionsModel_exists). These comparisons precede all inverse limits and hold
for empty schemes and identity morphisms as well. -/
theorem coefficientProjectionSectionsModels_exists
    {X Y : Scheme.{u}} (a : X ⟶ Y) :
    Nonempty (SectionsComposition l E a) ∧ Nonempty (SupportSections l E Y) := by sorry

end WeilConjectures.CoefProjectionEvaluation
