/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleData

/-! # The ordinary closed vertex as a finite-image Roos limit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary exact closed vertex agrees with the recorded direct-image tower of
completed restriction. This compares vertices only; it makes no constructibility,
linearity, open-complement, or distinguished-localization-triangle assertion.
Source: blueprint localization, closed-image paragraph; Bhatt--Scholze, Section 6.5;
Stacks 09AH and 099N(3)--(5)
(blueprint: lem-sf-integral-closed-kernel-roos).

Proof: the immersion completed-pullback comparison identifies the ordinary exact
restriction of the complete input with its completed integral pullback, through the
specified completion unit and finite quotient maps. Closed direct image is exact;
its termwise derived functor is its total right-derived functor. As a right adjoint
it preserves countable products and the derived limit. Apply it to the augmented
reduction Roos triangle of the complete pullback. The normalized coefficient
restriction/direct-image comparisons identify the terms with sfDirectImageTerm and
the transitions with sfDirectImageTransition. Transporting the distinguished Roos
triangle supplies a SfIntegralDirectImage with its projection and boundary, whose
vertex is isomorphic to the derived ordinary closed composite. No finite-type or
cohomological bound is needed for this comparison. The zero object and empty closed
subscheme cause no change: the corresponding products and triangles are zero. -/
theorem sfIntegralClosedKernel_roos
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    (hiK : IsSfDerivedComplete l E Z ((integralDerivedPullback l E i).obj K)) :
    letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
      integralOperationsDerivedCountableProducts l E X
    ∃ L : SfIntegralDirectImage l E i ((integralDerivedPullback l E i).obj K),
      Nonempty ((sfRecollementModuleClosed l E i).mapDerivedCategory.obj K ≅ L.obj) := by sorry

end WeilConjectures
