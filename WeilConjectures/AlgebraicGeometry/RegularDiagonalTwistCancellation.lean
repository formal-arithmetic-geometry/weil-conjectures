/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularDualizingTwistCancellation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

/-! # Specified twist cancellation in the finite root-line presentation

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Steps 1--2
(blueprint: lem-pur-regular-dualizing-twist-cancellation).

The ordered positive root powers are the recorded finite Tate objects. Cancellation
is characterized by its tensor/projection/counit equation. This fixes the arrow
uniquely and avoids choosing a comparison with an abstract `HasTateTwist` datum.
The original abstract-presentation declarations are reexported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The tensor/projection/counit characterization of the specified cancellation.
The left side tensors the exceptional adjunct of `φ` with the m-th root power.
The right side is precisely the given oriented dualizing comparison. Transposing
co-projection and cancelling its invertible m-th factor gives this equation.
Transport is universally quantified over its root- and pure-tensor-normalized
record, whose uniqueness is `ordinaryFiniteTwistTransport_unique`.
Source: `sk-thm-regular`, Steps 1--2, the displayed q, q-prime and Phi composites
(blueprint: lem-pur-regular-dualizing-twist-cancellation). -/
def RegularDiagonalComparisonEquation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] (aX : X ⟶ Spec (.of P.field.k))
    (m n c : ℕ) (h : n = m + c)
    (W_X : Etale.DerivedCategoryModule P.Coefficient X)
    (W_Z : Etale.DerivedCategoryModule P.Coefficient Z)
    (b : W_Z ≅ (rightDerivedUpperShriek P.Coefficient i).obj W_X)
    (P_X : W_X ≅ P.diagonalTwistEtale X n)
    (P_Z : W_Z ≅ P.diagonalTwistEtale Z m)
    (φ : ordinaryFiniteUnit P.Coefficient Z ⟶
      (rightDerivedUpperShriek P.Coefficient i).obj (P.diagonalTwistEtale X c)) : Prop :=
  ∀ t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates,
    ((ordinaryFiniteTensor P.Coefficient X).map
        ((rightDerivedUpperShriekAdjunction P.Coefficient i).homEquiv _ _ |>.symm φ)).app
          (P.diagonalTwistEtale X m) ≫
      (WeilConjectures.PurityFiniteSetting.compositionEtalePowerAdd
        P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates X c m).inv ≫
      (eqToIso (congrArg (P.diagonalTwistEtale X) ((Nat.add_comm c m).trans h.symm))).hom ≫
      P_X.inv =
    ((projectionMap (ModuleCat.{u + 1} P.Coefficient) i).app
        (ordinaryFiniteUnit P.Coefficient Z)).app (P.diagonalTwistEtale X m) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i).map
        ((derivedTensorLeftUnitor (ModuleCat.{u + 1} P.Coefficient) Z _).hom ≫
          (vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t i (P.diagonalExponent_isUnit aX) m).hom ≫
          P_Z.inv ≫ b.hom) ≫
      (rightDerivedUpperShriekAdjunction P.Coefficient i).counit.app W_X

/-- The specified cancellation exists uniquely in the concrete finite Tate
presentation, is invertible, and gives the negative c-th twist of Ri! A_X.
The orientations force the displayed W's to be bounded constructible of finite
Tor dimension, so their separate membership hypotheses are redundant here.
Source: `sk-thm-regular`, Steps 1--2
(blueprint: lem-pur-regular-dualizing-twist-cancellation).

Proof (postponed): form q by P_Z inverse, b, Ri! P_X and the invertible-twist
co-projection. Tensor by the actual dual of the m-th finite root power, then
apply evaluation, ordered-power addition, associativity and the unitors to obtain
q-prime. Apply the inverse c-th co-projection to get Phi. Under the exceptional
adjunction, tensoring this map by the m-th power is exactly the displayed
projection/counit equation. Conversely, tensoring by that invertible power and
adjunction are bijections on Hom, so the equation uniquely fixes Phi. Every
factor constructing Phi is invertible. Tensoring q-prime by the negative c-th
power gives Ri! A_X = A_Z(-c)[-2c]. Root inclusions and pure tensors uniquely
fix the transport record, so the equation holds for every normalized transport.
The zero powers are the coefficient unit, and on the empty scheme all arrows
are the unique arrows, so neither case requires an extra assumption. -/
theorem regular_diagonal_dualizing_twist_cancellation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] (aX : X ⟶ Spec (.of P.field.k))
    (m n c : ℕ) (h : n = m + c)
    (W_X : Etale.DerivedCategoryModule P.Coefficient X)
    (W_Z : Etale.DerivedCategoryModule P.Coefficient Z)
    (b : W_Z ≅ (rightDerivedUpperShriek P.Coefficient i).obj W_X)
    (P_X : W_X ≅ P.diagonalTwistEtale X n)
    (P_Z : W_Z ≅ P.diagonalTwistEtale Z m) :
    (∃! φ : ordinaryFiniteUnit P.Coefficient Z ⟶
        (rightDerivedUpperShriek P.Coefficient i).obj (P.diagonalTwistEtale X c),
      RegularDiagonalComparisonEquation P i aX m n c h W_X W_Z b P_X P_Z φ) ∧
    (∀ φ, RegularDiagonalComparisonEquation P i aX m n c h W_X W_Z b P_X P_Z φ →
      IsIso φ) ∧
    Nonempty ((rightDerivedUpperShriek P.Coefficient i).obj
      (ordinaryFiniteUnit P.Coefficient X) ≅
        P.functorialCupTarget false Z (-(2 * (c : ℤ))) (-(c : ℤ))) := by
  sorry

/-- The unique cancellation arrow characterized by the actual tensor/projection
and exceptional counit maps. Choice is applied to a uniquely determined morphism,
not to a bare isomorphism or Tate-line trivialization.
Source: `sk-thm-regular`, Steps 1--2, specified Phi
(blueprint: lem-pur-regular-dualizing-twist-cancellation). -/
noncomputable def regularDiagonalComparisonPhi
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] (aX : X ⟶ Spec (.of P.field.k))
    (m n c : ℕ) (h : n = m + c)
    (W_X : Etale.DerivedCategoryModule P.Coefficient X)
    (W_Z : Etale.DerivedCategoryModule P.Coefficient Z)
    (b : W_Z ≅ (rightDerivedUpperShriek P.Coefficient i).obj W_X)
    (P_X : W_X ≅ P.diagonalTwistEtale X n)
    (P_Z : W_Z ≅ P.diagonalTwistEtale Z m) :
    ordinaryFiniteUnit P.Coefficient Z ⟶
      (rightDerivedUpperShriek P.Coefficient i).obj (P.diagonalTwistEtale X c) :=
  (regular_diagonal_dualizing_twist_cancellation P i aX m n c h W_X W_Z b P_X P_Z).1.exists.choose

end AlgebraicGeometry.Etale
