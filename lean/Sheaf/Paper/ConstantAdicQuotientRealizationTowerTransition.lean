/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.BoundedConstructibleTower

/-! # Pullback of the consecutive adic tower transition

This is the tower-normalization substep of the consecutive quotient
realization argument.  It contains no constant realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- The pulled-back consecutive tower transition is an isomorphism.

Source: Stacks Project, proetale.tex, Tag 09C6, consecutive quotient
normalization.  Apply the supplied normalization isomorphism of the adic
tower at `(n+1,n)`, transport it through inverse image, and paste the
canonical scalar restriction comparison.  The resulting map is exactly the
displayed pulled-back transition, so it is invertible.  This statement is the
tower-only part of the realization reduction.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-tower-transition).
-/
theorem adicTowerPullback_consecutive_transition_iso
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) (W : Y.Etale) (_w : W.left) :
    Nonempty
      ((pbcDerivedExtend ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
        ((adicTowerPullback (W.hom ≫ g)
          ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1))) ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  sorry

end AlgebraicGeometry.Scheme
