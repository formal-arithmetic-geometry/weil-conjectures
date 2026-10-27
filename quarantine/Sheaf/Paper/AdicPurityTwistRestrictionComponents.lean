/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPurityRootComparisons
/-! # Components of the root-normalized restriction comparison
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: lem-pur-adic-twist-restriction-components).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
section TwistReduction
variable [hInvert : ∀ x : T, Invertible (l : T.residueField x)]
include hInvert

/-- Objectwise balanced tensor comparison for finite scalar restriction.
Source: def-coefficient-twists-detailed, finite coefficient line and tensor powers.
(blueprint: lem-pur-adic-twist-restriction-components).
Proof: use the prescribed root quotient on the second factor and the identity on
M. The resulting sectionwise pairing is balanced over the completed ring, so the
tensor and sheafification universal properties give a morphism. Trivialize the
integral root line on a pro-etale cover. The quotient map becomes the coefficient
projection, and the comparison becomes M tensor the scalar unit, hence an
isomorphism. Isomorphy is local and therefore descends. This also treats d = 0,
the zero module, the zero coefficient ring and the empty scheme. -/
theorem adicPurityTwistRestriction_component (d : ℕ)
    (M : scalarReductionTarget l E T n) :
    ∃ e : (integralSheafTwist l E T (d : ℤ)).obj
        ((scalarReductionRestriction l E T n).obj M) ≅
      (scalarReductionRestriction l E T n).obj
        ((SheafOfModules.siteSheafTensorRight
          (A := integralCoefficientCommRingSheaf l E T n)
          (finiteCoefficientTwist l E T n (d : ℤ))).obj M),
      ∀ (W : T.ProEtᵒᵖ) (x : M.val.obj W)
        (y : (integralTwistLine l E T (d : ℤ)).val.obj W),
        e.hom.val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted l E T) _ _ W x y) =
          SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W x
              ((adicPurityRootQuotients l E n T d).val.app W y) := by sorry

end TwistReduction
end WeilConjectures
