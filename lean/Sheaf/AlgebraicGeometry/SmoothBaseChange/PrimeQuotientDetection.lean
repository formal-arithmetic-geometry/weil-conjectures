/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Detecting a prime cyclic coefficient inside a nonzero ring quotient

Source: Stacks Project, Tag 03FD, with the vector-space retract argument needed
in the arbitrary-ring reading of the coefficient step in Tag 0F08.
(blueprint: lem-sbc-prime-quotient-detection)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Vanishing for Lambda/rLambda implies vanishing for the prime cyclic coefficient
whenever r is prime and is not a unit in Lambda.

Source: Stacks Project, Tag 03FD, module/abelian cohomology comparison;
Tag 0F08, proof's coefficient reduction, extended to arbitrary Lambda by the
following retract argument. This argument takes place in abelian sheaves, so
no Lambda-linear decomposition of a Lambda-module is asserted.
(blueprint: lem-sbc-prime-quotient-detection)

Proof:
1. Since r is not a unit, the ideal (r) is proper: if 1 belongs to it, writing
1 = a*r gives an inverse for r. Thus V = Lambda/rLambda is a nonzero vector
space over F_r. Its vector 1 is nonzero. Extend that vector to a basis, and
project onto its coordinate. The inclusion a -> a*1 and this projection exhibit
F_r as an additive retract of V.
2. Apply the constant abelian sheaf functor on Y to this retraction, and then
the abelian higher direct image in degree q along h. Functors preserve the
retraction identities, so R^q h_* F_r is a retract of R^q h_* V. A retract of
a zero object is zero.
3. Forgetting coefficients commutes with constant sheaves. Tag 03FD on every
etale object, followed by the sheafified cohomology-presheaf description of
higher direct images, identifies the underlying abelian higher direct images
with those of the module sheaves in the statement. Injective module resolutions
compute these comparisons because their underlying abelian terms are acyclic.
Finally the forgetful functor reflects zero objects. In prime coefficients the
quotient by r is the ring itself. These identifications turn step 2 into the
claimed implication. Negative degrees vanish, including for either coefficient
ring, and degree zero uses the ordinary direct-image comparison. -/
theorem isZero_prime_cyclic_higherDirectImage_of_quotient
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (r : ℕ) (hr : r.Prime) (hunit : ¬ IsUnit (r : Λ))
    (hzero : IsZero (higherDirectImage Λ h q (constantModSheaf Λ Y r))) :
    IsZero (higherDirectImage (ULift.{u + 1} (ZMod r)) h q
      (constantModSheaf (ULift.{u + 1} (ZMod r)) Y r)) := by sorry

end AlgebraicGeometry.Etale
