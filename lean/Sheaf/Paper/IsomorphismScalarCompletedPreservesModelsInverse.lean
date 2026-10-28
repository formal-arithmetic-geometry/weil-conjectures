/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModelBase

/-! Inverse-image preservation of good completed integral models.

The source is the inverse-image part of the proof of
`scalar_completed_preserves_models` (blueprint:
`lem-weil-isomorphism-scalar-completed-preserves-models`).  The statement is
separate because the independent site and coefficient universes require the
ringed-topos K-flat pullback argument for the sectionwise inverse-image model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The sectionwise inverse image sends every good representative to a good one.
Source: the inverse-image step of `lem-weil-isomorphism-scalar-completed-preserves-models`,
using the sectionwise inverse-image equivalence and the ringed-topos K-flat pullback
criterion (Stacks Tags 03DA, 06YN, and 0G7E).  The proof transports the K-flat
independent-coefficient condition and each flat term along the exact equivalence;
the coefficient map is the prescribed completed limit isomorphism, so no arbitrary
module or coefficient object is selected.
(blueprint: new-k3-isomorphism-scalar-completed-inverse-good).

Proof: Present the sectionwise inverse-image functor as an algebraic inverse image of ringed
topoi using the prescribed completed coefficient isomorphism. The site equivalence gives the
adjunction and finite-limit preservation. Apply the ringed-topos K-flat pullback theorem to
the given independent-coefficient K-flat complex and its flat terms; unfold
`integralOperationsGoodComplex` to obtain both clauses. -/
-- Proof implementation is the independent-universe sectionwise K-flat pullback step.
theorem inverseImageIntegralModules_preserves_good
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    integralOperationsGoodComplex l E X
      ((inverseComplex l E g).obj P.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
