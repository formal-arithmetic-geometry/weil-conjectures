/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteCore
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteSquares

/-! # Finite scalar tensor comparisons in the specified cochain presentations

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
(blueprint: lem-weil-isomorphism-scalar-finite-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The finite comparisons, canonical quotient maps and adjacent transition maps
for a supplied normalized completed chain comparison.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL; the coefficient
quotient calculation in Steps 4 and 5 of the original model argument.
(blueprint: lem-weil-isomorphism-scalar-finite-model).

Proof: Form the two ScalarQuotientChain.Tower records from the completed coefficient
rings, the finite coefficient rings, their actual projections, and their transitions.
The identity completedCoefficientMap followed by a projection equals the E projection
followed by integralScalarQuotientSheafMap; compatibility of the same-index quotient
maps gives the transition identity, including for ramified extensions. The finite
constant comparisons and their completed limits define Transport; their naturality
and projection equations verify its six commutative squares. Apply
scalar_quotient_chain_squares. Its ordinary scalar-extension functors and the chosen
finiteChangeData, unrestrictedIntegralReductionFunctor and integralScalarReduction
have the same prescribed sheafified tensor objects and maps. The object equalities
and map formulas therefore define natural presentation isomorphisms carrying their
pure tensors to finitePure, unrestrictedIntegralTensorSection and
integralScalarTensorSection. Transport the supplied completed comparison and its
CompletedFormula to the generic presentation, apply the generic finite theorem,
and transport its output back. Whisker with the inclusion of good complexes.
The forward reassociation formula sends s tensor (a tensor x) to
(c_L inverse(s) * iota(a)) tensor x. Quotients insert 1 in the middle factor and
reduce the outer scalar. Transitions reduce both finite scalars on the left and
the single scalar on the right. Naturality of presentation transport preserves the
quotient and transition squares. Restriction of scalars changes neither underlying
sections nor these maps, giving exactly the displayed formulas and equalities.
No projection is assumed surjective, and no coefficient map is assumed flat;
the lowest level, zero complexes, and empty sites obey the same tensor identities. -/
theorem scalar_finite_model
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
      (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
      (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n),
    FiniteFormula l E L ι g bfin ∧
    LeftQuotientFormula l E L ι g vleft ∧
    RightQuotientFormula l E L ι g vright ∧
    QuotientSquare l E L ι g b bfin vleft vright ∧
    LeftTransitionFormula l E L ι g tleft ∧
    RightTransitionFormula l E L ι g tright ∧
    TransitionSquare l E L ι g bfin tleft tright := by
  obtain ⟨bfin, vleft, vright, tleft, tright, hF, hL, hR, hTL, hTR⟩ :=
    scalar_finite_core l E L ι g b hb
  obtain ⟨hQ, hT⟩ := scalar_finite_squares l E L ι g b bfin vleft vright tleft tright
    hb hF hL hR hTL hTR
  exact ⟨bfin, vleft, vright, tleft, tright, hF, hL, hR, hQ, hTL, hTR, hT⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
