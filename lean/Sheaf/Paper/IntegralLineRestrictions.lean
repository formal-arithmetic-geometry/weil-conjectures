/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.IntegralLineReductionDefinitions

/-! # Restriction of signed integral line tensor

(blueprint: lem-pur-integral-line-restrictions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Ordinary signed-line tensor preserves completeness, and its evaluations restrict
and transport to the integral category through the actual completion comparisons.
Source: Bhatt--Scholze 3.4.12, 3.5.1 and 3.5.2; blueprint proof (3).
(blueprint: lem-pur-integral-line-restrictions).

Proof: the opposite-line pairing makes exact tensor a triangulated equivalence,
which preserves products. Balance tensor past each reduction, with its quotient
transitions and reduction units. Transport the canonical augmented Roos triangle:
the first map is still exactly the reduction units and the second is 1 minus the
quotient shift. Thus ordinary tensor preserves completeness. For each finite
reduction its cohomology is the old cohomology tensored with the finite signed
line. Refine a finite constructible partition by a line-trivializing cover; its
finite model is M tensor A, isomorphic to M. Hence constructibility and the same
uniform support interval are preserved. The actual completion comparison is an
isomorphism on these complete objects, giving the completed membership statement
and the natural comparison c. Localize the ordinary evaluations on good models;
association and evaluation give the stated chain evaluation formula. The two
triangle identities hold on pure tensors and descend by localization. Fullness
restricts this equivalence and both evaluations to the integral subcategory.
Conjugate by c to obtain the completed functors and evaluations. Naturality cancels
successive inverse comparisons in both triangle identities. These are precisely
the two displayed evaluation equations in CompletedRestriction. -/
theorem integral_line_restrictions
    (hl : ∀ x : X, Invertible (l : X.residueField x))
    (L : scalarReductionSource.{u, u} l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (hfinite : FiniteReductions l E X L)
    (e : Evaluations l E X L) (he : EvaluationFormula l E X L e) :
    (∀ (m : ℤ) (K : D.{u, u} l E X none), IsComplete l E X none K →
      IsComplete l E X none ((ordinary l E X L m).obj K)) ∧
      Restrictions l E X L e := by
  sorry

end WeilConjectures.IntegralLineReduction
