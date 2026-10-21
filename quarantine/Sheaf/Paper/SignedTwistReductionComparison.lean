/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction

/-! # Normalized reduction of signed completed Tate lines

Source: prop-weil-twist-preserves, proof steps 1 and 6.
(blueprint: lem-weil-signed-twist-reduction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

/-- Reduction respects signed powers, dual evaluation, and exact derived line tensor.
Source: blueprint prop-weil-twist-preserves, proof steps 1 and 6
(blueprint: lem-weil-signed-twist-reduction-comparison).

Proof: the integral first line reduces to its prescribed finite line by the original
quotient tensor construction. The reduction of the unit is the coefficient projection.
Tensor these maps recursively to obtain the positive powers. For a negative power,
use the unique map of duals compatible with the evaluation pairing. On a cover
trivializing the integral line these maps are the quotient coefficient maps, and
the induced scalar extensions are the identity on the quotient coefficient unit.
Thus all induced extension maps are isomorphisms. They glue because their equations
on tensors and evaluations are independent of the local basis. These equations also
prove uniqueness, first at zero and one, then by induction on positive powers and
by nondegeneracy of the dual pairing at negative powers. For derived comparisons,
resolve K by a flat-term K-flat complex P. Exact line tensor preserves K-flatness
and flat terms. Reduction of P is K-flat over the quotient ring. Rebracketing sends
(x tensor y) tensor a to (x tensor a) tensor (y tensor 1), and its inverse multiplies
the two quotient coefficients. The balanced maps commute with differentials and
with every chain map, so descend to the displayed natural derived isomorphism.
The same computation on the flat degree-zero line gives the single-object comparison.
All formulas commute with quotient transitions and the unit augmentations. -/
theorem signedTwistReduction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ, ∃! c : (∀ k : ℤ, integralTwistLine l E S k ⟶
      (scalarReductionRestriction l E S n).obj (finiteCoefficientTwist l E S n k)),
    ((∀ (U : S.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U),
    (c 0).val.app U a = (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U),
    (c 1).val.app U x = ((((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E S n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient S l E n) (purTwistIntegralOne S l E))).app U)
      ((1 : (integralCoefficientSheaf l E S n).obj.obj U) ⊗ₜ[
        (purTwistIntegralConstant S l E).obj.obj U,
        ((purTwistIntegralQuotient S l E n).hom.app U).hom] x))) ∧
  (∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U)
      (y : (purTwistIntegralModule S l E).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
      (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := integralCoefficientCommRingSheaf l E S n) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine l E S (Int.negSucc k)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U),
    (((c (Int.negSucc k)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
      ((c (Int.ofNat (k + 1))).val.app U x) =
      (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)) ∧
    ∀ k : ℤ, ∃! α : (scalarReductionExtension l E S n).obj
        (integralTwistLine l E S k) ≅ finiteCoefficientTwist l E S n k,
      ∀ (U : S.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
          (x : (integralTwistLine l E S k).val.obj U),
        α.hom.val.app U (sfReductionTensor l E S n (integralTwistLine l E S k) U a x) =
          a • (@id ((finiteCoefficientTwist l E S n k).val.obj U) ((c k).val.app U x))) ∧
    (∀ k : ℤ, ∀ n : ℕ, Nonempty ((scalarReductionDerivedExtension l E S n).obj
      (sfIntegralTwistingObject l E S k) ≅
        (DerivedCategory.singleFunctor _ 0).obj (finiteCoefficientTwist l E S n k))) ∧
    ∀ (m : ℤ) (n : ℕ), Nonempty (sfIntegralTwistingFunctor l E S m ⋙
      scalarReductionDerivedExtension l E S n ≅
      scalarReductionDerivedExtension l E S n ⋙ finiteComplexTwist l E S n m) := by
  sorry

end WeilConjectures
