/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData

/-! # strictCoefficientEquations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- strictCoefficientEquations: the indicated part of the ordered comparison argument.
Source: blueprint completed-exchange-coherence, second proof paragraph;
Stacks Tags 099M, 099N, 0A07 and 0E48.
(blueprint: lem-weil-pbc-ordered-strict-coefficient-equations).
Proof: the diagonal exact-adjunction comparison identifies the completed strict
exchange with the reduction of the ambient mate. The perfect quotient projection
maps are invertible, so conjugating gives the first formula. For the second,
transpose the projection formula map under the ordinary ringed adjunction.
Restriction identifies its counit with the constant counit, and quotient balancing
sends each pure tensor to the same tensor. Apply the derived pullback and tensor
comparison to this equation on the single strict quotient diagram. Tensor descent
makes it an equality of derived tower morphisms. For the third, transpose the
restricted strict exchange under the constant tower adjunction. Scalar restriction
identifies both units and counits, and coefficient inverse image respects
composition. The transpose is therefore the transpose defining the constant mate.
Bijectivity of the adjunction correspondence gives the equation. Naturality for
rho then gives exactly beta and delta at the reduced complete input. No claim of
faithfulness of derived evaluation functors is used. -/
theorem strictCoefficientEquations (sq : ChosenCartesianSquare g' f' f g) :
    ∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) := by sorry

end AlgebraicGeometry.Scheme.OrderedExchange
