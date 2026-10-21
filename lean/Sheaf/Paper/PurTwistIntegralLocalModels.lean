/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.PurTwistSheaves
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Integral and finite local models of the scalar-extended root line

Source: coefficient-twist blueprint, proof steps 6--8 and 10.
(blueprint: lem-pur-twist-integral-local-models)
-/

@[expose] public section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Scalar extension of the completed root line has local bases and ordinary
finite quotients with finite étale local models.

Source: coefficient-twist blueprint, proof steps 6--8 and 10; Stacks Project,
Tags 03EK, 03PK and 03RV.
(blueprint: lem-pur-twist-integral-local-models)

Proof: the canonical coefficient comparison is the completed scalar pushout.
On a cover trivializing the completed root line, its prescribed scalar tensor is
the completed valuation-ring module of rank one; the action is the specified
completed action because both scalar factors have the prescribed tensor formula.
Ordinary reduction is the quotient by the indicated uniformizer power on either
presentation, giving the stated comparison with the original discrete integral
tensor reduction. Each finite coefficient quotient is killed by some l-power,
because l is a unit times a positive uniformizer power. Choose such a level of
the finite root tower and its étale primitive-root cover. On this cover the finite
integral tensor has one basis element over the constant finite quotient ring.
This is a locally constant finite model. Each geometric point lifts to a member
of the étale cover, and localization and constant-stalk comparison identify its
stalk with that quotient ring. It is finite, and is nonzero at every geometric
point because the exponent is positive. The single stratum equal to the whole
scheme, with identity immersion, witnesses constructibility; the canonical
identity pullback preserves the displayed local models and the finite stalks.
If the base is nonempty, a geometric point exists, and its nonzero stalk implies
that the sheaf is nonzero. For the empty scheme the last assertion is conditional
and all constructions still have their prescribed zero values. -/
theorem purTwistIntegralLocalModels
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)]
    (hL : (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1) :
    (∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty ((purTwistIntegralModule S l E).over (U i) ≅
        (SheafOfModules.unit
          (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S)).over (U i))) ∧
    ∀ n : ℕ,
      Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
          (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i, Nonempty ((purTwistFiniteOne S l E n).over (U i) ≅
          (SheafOfModules.unit (WeilConjectures.integralCoefficientSheaf l E S n)).over (U i))) ∧
      (Nonempty S → ¬IsZero (purTwistFiniteOne S l E n)) := by
  sorry

end AlgebraicGeometry.Scheme
