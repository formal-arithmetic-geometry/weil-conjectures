/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.DlLocallyConstructibleAdicHeart

/-! # Invertibility of the actual shifted coefficient lines

Source: current blueprint, sk-lem-sf-twist-interchange, proof final paragraph.
(blueprint: lem-sf-shifted-coefficient-lines-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The specified signed Tate lines lie in the finite-Tor domains and are invertible
for their recorded tensor structures. This only asserts the line property; it makes
no assertion about internal Hom comparison maps or their naturality.
Source: current blueprint, sk-lem-sf-twist-interchange, proof final paragraph;
coefficient-twists-detailed, signed powers and scalar extensions
(blueprint: lem-sf-shifted-coefficient-lines-invertible).

Proof: the normalized opposite-line contractions of
lem-sf-perfect-dual-pair-and-tate-stability identify the tensor of the signed line
of exponent m with the line of exponent -m with the coefficient unit, in both
orders. Identify their representatives with the signed powers in
sfIntegralTwistingCoefficient, and shift the opposite factor by -t. In the ordinary
model this is the shifted single complex of the same rank-one sheaf, and the
Koszul shift constraints give the normalized contractions; their signs are units
also for odd t and in characteristic two. Rank one gives Tor amplitude [0,0]
before shifting and hence finite Tor amplitude after shifting. The fully faithful
integral closed-model embedding reflects these contraction isomorphisms, giving
the integral assertion for the actual shifted line. Apply the specified integral
reduction and its closed comparison to obtain the finite assertion; the ordinary
finite model identifies the reduced representative with that same signed finite
line. Apply rationalization and its closed comparison to obtain the rational
assertion, using its shift comparison to identify the image with the displayed
shift of sfRationalTwistingCoefficient. Finally perform this rational argument at
the least finite coefficient field representing sfQbarTwistingCoefficient and use
commonClosedComparison. Its shift comparison and common-stage tensor normalization
identify the image with the displayed common-stage line. In each case the
opposite signed shifted line and the two contractions supply IsInvertible.
For m = 0 these are the unit constraints; negative m exchanges the line and its
dual. The argument is local and also applies to the empty scheme. -/
theorem sfShiftedCoefficientLinesInvertible
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {n : ℕ}
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    (X : SixFunctorSpace D) (m t : ℤ) :
    (∃ hL : S.toSixFunctorOperationDatum.finiteTorDomain X
        ((sixFunctorIntegralReduction D C E n X).obj
          ((@sfIntegralTwistingCoefficient C.l _ E _ _ _ X.obj.left
            (dlAdicGeometricResidueInvertible D C X.obj.left) m)⟦t⟧)),
      @IsInvertible _ _ (S.finiteClosed X).closed.monoidal ⟨_, hL⟩) ∧
    (∃ hL : S.toSixFunctorOperationDatum.integralFiniteTorDomain X
        ((@sfIntegralTwistingCoefficient C.l _ E _ _ _ X.obj.left
          (dlAdicGeometricResidueInvertible D C X.obj.left) m)⟦t⟧),
      @IsInvertible _ _ (S.integralClosed X).closed.monoidal ⟨_, hL⟩) ∧
    (∃ hL : (⊤ : ObjectProperty (sfRationalConstructibleCategory C.l E X.obj.left))
        ((@sfRationalTwistingCoefficient C.l _ E _ _ _ X.obj.left
          (dlAdicGeometricResidueInvertible D C X.obj.left) m)⟦t⟧),
      @IsInvertible _ _ (S.rationalClosed X).closed.monoidal ⟨_, hL⟩) ∧
    (∃ hL : (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left))
        ((@sfQbarTwistingCoefficient C.l _ X.obj.left
          (dlAdicGeometricResidueInvertible D C X.obj.left) C.Qbar _ _ _ m)⟦t⟧),
      @IsInvertible _ _ (S.commonClosed X).closed.monoidal ⟨_, hL⟩) := by sorry

end WeilConjectures
