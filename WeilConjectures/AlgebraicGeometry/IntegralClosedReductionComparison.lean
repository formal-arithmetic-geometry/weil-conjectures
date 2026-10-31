/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralSupportNormalizationData

/-! # Invertibility of the strict closed reduction square

Source: smooth-purity localization, integral support comparison; Stacks 0941 and 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized ordinary immersion comparison gives an invertible strict reduction
square, on the entire ambient derived category.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md, integral
support comparison; Stacks Tags 0941, 099N(2),(5) and 06YY.
(blueprint: lem-sf-closed-reduction-comparison).

Proof: represent an arbitrary input by a K-flat complex with flat terms, as in
integralOperationsGoodLocalization. The pull_model clause of C identifies its pull
map with the quotient augmentation into the strict Roos complex: its first coordinate
is the ordinary pullback of the quotient unit, transposed through the ordinary
adjunction, and its homotopy coordinate is zero. Applying the actual derived reduction
and its specified reconstruction counit identifies the composite closedReduction
with levelwise ordinary pullback followed by the finite coefficient pullback map.
This is an isomorphism: the coefficient inverse-image identifications commute with
the quotient maps, and immersion inverse image is exact. The flat representative
computes these derived tensors without further choices. All transitions are the
actual quotient transitions, so this identification is in the derived system category.
Alternatively its cone evaluates to an acyclic complex at every index, hence has
zero cohomology as a system and is zero. Thus the strict square is invertible.
Localization and naturality extend this conclusion from good representatives to
all objects; objectwise invertibility gives an isomorphism of functors. The argument
includes the empty closed scheme and the zero input. -/
theorem closedReduction_isIso {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (C : SfOrdinaryIntegralComparison l E i) :
    IsIso (closedReduction l E i C) := by sorry

end WeilConjectures.IntegralSupportNormalization
