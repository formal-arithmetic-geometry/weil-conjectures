/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedEExchangeMate

/-! # Normalization of canonical realization exchange
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Tag 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.CondensedERealization
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
variable (D : Data l E k)
variable {X' X Y' Y : Base k}
variable {g' : X'.scheme ⟶ X.scheme} {f' : X'.scheme ⟶ Y'.scheme}
  {f : X.scheme ⟶ Y.scheme} {g : Y'.scheme ⟶ Y.scheme}
variable [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- Ambient normalization of the canonical integral mate.
Source: Stacks Tag 07A7; the completed exchange unit and pullback reflection.
(blueprint: lem-weil-pbc-condensed-e-integral-mate-normalization)
Proof. Define the ordinary-to-integral pull comparison by the completion unit
followed by pullAmbient.inv. Postcompose with pullAmbient and use naturality and
integralComp_normalization to reduce its compositor equation to completedPullComp_unit.
Transport this equation along the equality of the two composite scheme morphisms.
The generic composition-square cancellation lemma identifies the resulting square.
The ordinary square is the ambient ringed square by expansion of pullComp and the
coefficient equality transports. Transpose both mates under the ordinary adjunction:
the supplied integral_counit equations and naturality identify their adjuncts.
Thus the integral mate precomposed by the ordinary completion unit equals ordinary
exchange followed by that unit at the other corner. completedExchange_unit gives
the same formula for the ordered completed exchange. Move pushAmbient through the
unit by naturality and cancel the ambient isomorphisms. Finally completedPull_reflection
makes precomposition with the unit injective into the target: completed pullback has
complete output and direct image preserves completeness. This proves the displayed
equality without any claim of invertibility of exchange or completeness of the input. -/
theorem integralMate_normalization (sq : ChosenCartesianSquare g' f' f g)
    (K : Integral l E X.scheme) :
    ((integralMate l E k D sq.toCommSq).app K).hom ≫
        (D.along X' Y' f').pushAmbient.hom.app ((D.along X' X g').pull.obj K) ≫
        ((pbcIntegralDatum l E).push f').map
          ((D.along X' X g').pullAmbient.hom.app K) =
      (D.along Y' Y g).pullAmbient.hom.app ((D.along X Y f).push.obj K) ≫
        ((pbcIntegralDatum l E).completedPull g).map
          ((D.along X Y f).pushAmbient.hom.app K) ≫
        (pbcIntegralDatum l E).completedExchange sq K.obj := by
  sorry

end WeilConjectures.CondensedERealization
