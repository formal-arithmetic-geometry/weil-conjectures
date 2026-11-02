/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData

/-! # Reduction adjunction before choosing tensor presentations

Source: Stacks 06YS, 06YY, 07A6 and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The sequence projection supplies the reduction adjunction and its finite models,
independently of every choice of tensor presentation.
Source: Stacks 06YS, 06YY, 07A6 and 0941.

Proof: apply SequenceProjection.pushforwardLimitProjections to the completed
coefficient ring, the quotient ring tower, and the completion projections. Transport
its ordinary strict systems through strictSystemSequenceEquivalence and derive that
exact equivalence. The restricted-tower functor is naturally identified with
coefficientSequenceRestriction: both have the same completed-linear sections and
quotient transitions. Uniqueness of right derived functors identifies the theorem's
right adjoint with coefficientSequenceLimit. This identification preserves each
projection, by the defining right-derived descent equation for
coefficientConstantTowerProjection and the exact evaluation factors.
Transport the adjunction through this identification. Uniqueness of the left
derived extension at each level identifies its evaluated left adjoint with
coefficientFiniteDerivedExtension, preserving its universal K-flat counit. The
normalized derived level adjunction is therefore coefficientFiniteAdjunction.
The counit projection clause of pushforwardLimitProjections now gives the displayed
Hom-equivalence equation. For a flat-term K-flat Q take the ordinary sequence
extension of Q, and localize its universal left-derived counit. Its finite components
are the scalar-extension counits and its transitions send b tensor x to rho(b)
tensor x; uniqueness of the ordinary scalar model gives precisely
CoefficientReductionModels. Finally the transition adjunct for reduction identifies
with the derived associativity isomorphism B_n tensor over B_m (B_m tensor over A Q)
= B_n tensor over A Q. It is invertible. The finite scalar adjunction converts this
into the universal Hom-bijection defining IsNormalizedCoefficientSequence. This also
covers equal levels, the zero complex, and the empty scheme.
(blueprint: lem-coef-sequence-reduction-adjunction)
-/
theorem coefficientSequenceReductionAdjunction_exists :
    ∃ (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
      (adj : L ⊣ coefficientSequenceLimit l E W)
      (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
        coefficientFiniteDerivedExtension l E W n),
      CoefficientReductionModels l E W L ρ ∧
      (∀ P, IsNormalizedCoefficientSequence l E W (L.obj P)) ∧
      ∀ (N : coefficientSequenceDerived l E W) (n : ℕ),
        (coefficientFiniteAdjunction l E W n).homEquiv _ _
          ((ρ n).inv.app ((coefficientSequenceLimit l E W).obj N) ≫
            (coefficientSequenceDerivedEvaluation l E W n).map (adj.counit.app N)) =
          (coefficientSequenceProjection l E W n).app N := by sorry

end WeilConjectures
